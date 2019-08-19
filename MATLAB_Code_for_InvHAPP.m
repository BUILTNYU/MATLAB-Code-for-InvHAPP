function [Objectives,Arrivals,e1,f1,y,x1,fval,S,exitflag,numiter,C,Pe,Pl,XTYCP,Aprime,bprime,bf]=InvHAPPfinal(X,T,Y,Net_Time,Net_Cost,Activities,Vehicles,Cost_Budget,Time_Budget,Sojourn,Dval,weight,c)

%should solve for objective coefficients Objectives given X, T, Y
%Net_Time is the travel time matrix of travel from each node to
%another node
%Net_Cost is the cost matrix of traversing from node to node
%Activities is the set of activities to be performed, along with their
%other information:
%       Column 1: activity ID
%       Column 2: node index of activity
%       Column 3: duration of activity
%       Column 4: early start time
%       Column 5: late start time
%       Column 6: early return home time
%       Column 7: late return home time
%The first activity is Home, and always has a positive utility; 
%Vehicles is a scalar # of vehicles
%Cost_Budget is a scalar budget
%Time_Budget is a vector Vx1 of travel time budget allocated to each member of
%the household
%w is a 6x1 vector of the weights of the objective function
%c is a 6x1 vector of the starting weights of the objectives, 0 or -1 (since is minimization): 1a - 1f
%Sojourn is a boolean: 1 if counting # sojourns, 0 if accumulating time
%away from home
%Dval is max # of sojourns or time spent away from home on a tour

bigM=10000;
N=size(Activities,1)*2;
Pplus=(N-2)/2;  %note that Pminus = Pplus (since this is size of each set)
%objective is all the X's sorted by vehicles, u, then w, and then T's in P,
%then T_0 by vehicle and T_2N+1 by vehicle
f=zeros(1,Vehicles*N*N+N-2+Vehicles*2);
f=[f zeros(1,2*Pplus)]; %this accounts for the Y's
numVar=size(f,2);
lb=zeros(1,numVar);
ub=zeros(1,numVar)+inf;

A=zeros(1,numVar);
Aeq=zeros(1,numVar);

%constraint (2)
%first equality constraint
for v=1:Vehicles
    Aeq(1,(v-1)*N^2+N+1:(v-1)*N^2+N+N)=1;
end
beq=1;
ieq=1;
for u=2:Pplus
    Aeq=[Aeq; zeros(1,numVar)];
    beq=[beq; 1];
    ieq=ieq+1;
    for v=1:Vehicles
        Aeq(ieq,(v-1)*N^2+u*N+1:(v-1)*N^2+u*N+N)=1; %note that it's u instead of u-1 because of Pplus
    end
end

%constraint (3)
for v=1:Vehicles
    for u=1:2*Pplus
        Aeq=[Aeq; zeros(1,numVar)];
        beq=[beq; 0];
        ieq=ieq+1;
        Aeq(ieq,(v-1)*N^2+u*N+1:(v-1)*N^2+u*N+N)=1;
        for w=1:N
            Aeq(ieq,(v-1)*N^2+(w-1)*N+u+1)=-1;
        end
    end
end

%constraint (4)
for v=1:Vehicles
    Aeq=[Aeq; zeros(1,numVar)];
    beq=[beq; 1];
    ieq=ieq+1;
    Aeq(ieq,(v-1)*N^2+2:(v-1)*N^2+Pplus+1)=1;
end

%constraint (5)
for v=1:Vehicles
    Aeq=[Aeq; zeros(1,numVar)];
    beq=[beq; 1];
    ieq=ieq+1;
    for u=1:Pplus  %negative
        Aeq(ieq,(v-1)*N^2+(u+Pplus)*N+N)=1;
    end
end

%constraint (6)
for v=1:Vehicles
    for u=1:Pplus
        Aeq=[Aeq; zeros(1,numVar)];
        beq=[beq; 0];
        ieq=ieq+1;
        for w=1:N
            Aeq(ieq,(v-1)*N^2+(w-1)*N+u+1)=1;
            Aeq(ieq,(v-1)*N^2+(w-1)*N+Pplus+u+1)=-1;
        end
    end
end

%constraint (7)
%this is the first inequality constraint
A(1,Vehicles*N*N+1)=1;
A(1,Vehicles*N*N+1+Pplus)=-1;
b=-Activities(2,3)-Net_Time(Activities(2,2),Activities(1,2));
ineq=1;

for u=2:Pplus
    A=[A; zeros(1,numVar)];
    b=[b; 0];
    ineq=ineq+1;
    A(ineq,Vehicles*N*N+u)=1;
    A(ineq,Vehicles*N*N+u+Pplus)=-1;
    b(ineq,1)=-Activities(u+1,3)-Net_Time(Activities(u+1,2),Activities(1,2));
end

%constraint (8)
for v=1:Vehicles
    for u=1:2*Pplus
        for w=1:2*Pplus
            A=[A; zeros(1,numVar)];
            b=[b; 0];
            ineq=ineq+1;
            A(ineq,(v-1)*N^2+u*N+w+1)=bigM; %X
            A(ineq,Vehicles*N^2+u)=1;
            A(ineq,Vehicles*N^2+w)=A(ineq,Vehicles*N^2+w)-1;
            if and(u>Pplus,w>Pplus)
                b(ineq,1)=bigM-Activities(1,3)-Net_Time(Activities(1,2),Activities(1,2));
            elseif and(u>Pplus,w<=Pplus)
                b(ineq,1)=bigM-Activities(1,3)-Net_Time(Activities(1,2),Activities(w+1,2));
            elseif and(u<=Pplus,w>Pplus)
                b(ineq,1)=bigM-Activities(u+1,3)-Net_Time(Activities(u+1,2),Activities(1,2));
            else
                b(ineq,1)=bigM-Activities(u+1,3)-Net_Time(Activities(u+1,2),Activities(w+1,2));
            end
        end
    end
end

%constraint (9)
for v=1:Vehicles
    for w=1:Pplus
        A=[A; zeros(1,numVar)];
        b=[b; 0];
        ineq=ineq+1;
        A(ineq,(v-1)*N^2+w+1)=bigM; %X
        A(ineq,Vehicles*N^2+N-2+v)=1;
        A(ineq,Vehicles*N^2+w)=-1;
        b(ineq,1)=bigM-Net_Time(Activities(1,2),Activities(w+1,2));
    end
end

%constraint (10) - duration for home activities should be 0
for v=1:Vehicles
    for u=1:Pplus  %negative
        A=[A; zeros(1,numVar)];
        b=[b; 0];
        ineq=ineq+1;
        A(ineq,(v-1)*N^2+(u+Pplus+1)*N)=bigM; %X
        A(ineq, Vehicles*N^2+Pplus+u)=1;
        A(ineq,Vehicles*N^2+N-2+Vehicles+v)=-1;
        b(ineq,1)=bigM-Activities(1,3)-Net_Time(Activities(1,2),Activities(1,2)); %duration = 0 at home
    end
end

%constraint (11) - for soft time windows we will relax this set of
%constraints
for u=1:2*Pplus
    if u>Pplus
        lb(1,Vehicles*N^2+u)=Activities(u-Pplus+1,6);
        ub(1,Vehicles*N^2+u)=Activities(u-Pplus+1,7);
    end
end

%constraint (12) & (13)
for v=1:Vehicles
    lb(1,Vehicles*N^2+N-2+v)=Activities(1,4);
    ub(1,Vehicles*N^2+N-2+v)=Activities(1,5);
    lb(1,Vehicles*N^2+N-2+Vehicles+v)=Activities(1,6);
    ub(1,Vehicles*N^2+N-2+Vehicles+v)=Activities(1,7);
end

%constarint (14) - use 2 inequality constraints to represent 1 equality
%constraint
for v=1:Vehicles
    for u=1:2*Pplus
        for w=1:Pplus
            %first <= ineq
            A=[A; zeros(1,numVar)];
            b=[b; 0];
            ineq=ineq+1;
            A(ineq,(v-1)*N^2+u*N+w+1)=bigM; %X
            A(ineq,Vehicles*N*N+N-2+Vehicles*2+u)=1;
            A(ineq,Vehicles*N*N+N-2+Vehicles*2+w)=A(ineq,Vehicles*N*N+N-2+Vehicles*2+w)-1;
            if Sojourn==1
                b(ineq,1)=bigM-1;
            else
                if u>Pplus
                    b(ineq,1)=bigM-(Activities(1+w,3)+Net_Time(Activities(1,2),Activities(1+w,2)));
                else
                    b(ineq,1)=bigM-(Activities(1+w,3)+Net_Time(Activities(1+u,2),Activities(1+w,2)));
                end
            end
            %next >= ineq
            A=[A; zeros(1,numVar)];
            b=[b; 0];
            ineq=ineq+1;
            A(ineq,(v-1)*N^2+u*N+w+1)=bigM; %X
            A(ineq,Vehicles*N*N+N-2+Vehicles*2+u)=-1;
            A(ineq,Vehicles*N*N+N-2+Vehicles*2+w)=A(ineq,Vehicles*N*N+N-2+Vehicles*2+w)+1;
            if Sojourn==1
                b(ineq,1)=bigM+1;
            else
                if u>Pplus
                    b(ineq,1)=bigM+(Activities(1+w,3)+Net_Time(Activities(1,2),Activities(1+w,2)));
                else
                    b(ineq,1)=bigM+(Activities(1+w,3)+Net_Time(Activities(1+u,2),Activities(1+w,2)));
                end
            end
        end
    end
end            
            
%constarint (15) - use 2 inequality constraints to represent 1 equality
%constraint
for v=1:Vehicles
    for u=1:2*Pplus
        for w=1:Pplus %negative
            %first <= ineq
            A=[A; zeros(1,numVar)];
            b=[b; 0];
            ineq=ineq+1;
            A(ineq,(v-1)*N^2+u*N+Pplus+1+w)=bigM; %X
            A(ineq,Vehicles*N*N+N-2+Vehicles*2+u)=1;
            A(ineq,Vehicles*N*N+N-2+Vehicles*2+Pplus+w)=A(ineq,Vehicles*N*N+N-2+Vehicles*2+Pplus+w)-1;
            if Sojourn==1
                b(ineq,1)=bigM+1;
            else    %THIS PORTION IS BROKEN - REPEAT, BROKEN - DON'T USE SOJOURN=0
                if u>Pplus
                    b(ineq,1)=bigM+(Activities(1+w,3)+Net_Time(Activities(1,2),Activities(1+w,2)));
                else
                    b(ineq,1)=bigM+(Activities(1+w,3)+Net_Time(Activities(1+u,2),Activities(1+w,2)));
                end
            end
            %next >= ineq
            A=[A; zeros(1,numVar)];
            b=[b; 0];
            ineq=ineq+1;
            A(ineq,(v-1)*N^2+u*N+Pplus+1+w)=bigM; %X
            A(ineq,Vehicles*N*N+N-2+Vehicles*2+u)=-1;
            A(ineq,Vehicles*N*N+N-2+Vehicles*2+Pplus+w)=A(ineq,Vehicles*N*N+N-2+Vehicles*2+Pplus+w)+1;
            if Sojourn==1
                b(ineq,1)=bigM-1;
            else
                if u>Pplus
                    b(ineq,1)=bigM-(Activities(1+w,3)+Net_Time(Activities(1,2),Activities(1+w,2)));
                else
                    b(ineq,1)=bigM-(Activities(1+w,3)+Net_Time(Activities(1+u,2),Activities(1+w,2)));
                end
            end
        end
    end
end  

%constraint (16)
for v=1:Vehicles
    for w=1:Pplus
        %first <= ineq
        A=[A; zeros(1,numVar)];
        b=[b; 0];
        ineq=ineq+1;
        A(ineq,(v-1)*N^2+w+1)=bigM; %X
        A(ineq,Vehicles*N*N+N-2+Vehicles*2+w)=-1;
        if Sojourn==1
            b(ineq,1)=bigM-1;
        else
            b(ineq,1)=bigM-(Activities(1+w,3)+Net_Time(Activities(1,2),Activities(1+w,2)));
        end
        %next >= ineq
        A=[A; zeros(1,numVar)];
        b=[b; 0];
        ineq=ineq+1;
        A(ineq,(v-1)*N^2+w+1)=bigM; %X
        A(ineq,Vehicles*N*N+N-2+Vehicles*2+w)=1;
        if Sojourn==1
            b(ineq,1)=bigM+1;
        else
            b(ineq,1)=bigM+(Activities(1+w,3)+Net_Time(Activities(1,2),Activities(1+w,2)));
        end
    end
end 

%constraint (17)
ub(1,Vehicles*N^2+N-2+Vehicles*2+1:Vehicles*N^2+N-2+Vehicles*2+Pplus)=Dval;

%constraint (18)
ub(1,1:Vehicles*N^2)=1;

%constraint (19)
A=[A; zeros(1,numVar)];
b=[b; Cost_Budget];
ineq=ineq+1;
for v=1:Vehicles
    for u=1:N
        for w=1:N
            if and(u>Pplus+1,w>Pplus+1)
                A(ineq,(v-1)*N^2+(u-1)*N+w)=Net_Cost(Activities(1,2),Activities(1,2));
            elseif and(u>Pplus+1,w<=Pplus+1)
                A(ineq,(v-1)*N^2+(u-1)*N+w)=Net_Cost(Activities(1,2),Activities(w,2));
            elseif and(u<=Pplus+1,w>Pplus+1)
                A(ineq,(v-1)*N^2+(u-1)*N+w)=Net_Cost(Activities(u,2),Activities(1,2));
            else
                A(ineq,(v-1)*N^2+(u-1)*N+w)=Net_Cost(Activities(u,2),Activities(w,2));
            end
        end
    end
end

%constraint (20)
for v=1:Vehicles
    A=[A; zeros(1,numVar)];
    b=[b; Time_Budget(v,1)];
    ineq=ineq+1;
    for u=1:N
        for w=1:N
            if and(u>Pplus+1,w>Pplus+1)
                A(ineq,(v-1)*N^2+(u-1)*N+w)=Net_Time(Activities(1,2),Activities(1,2));
            elseif and(u>Pplus+1,w<=Pplus+1)
                A(ineq,(v-1)*N^2+(u-1)*N+w)=Net_Time(Activities(1,2),Activities(w,2));
            elseif and(u<=Pplus+1,w>Pplus+1)
                A(ineq,(v-1)*N^2+(u-1)*N+w)=Net_Time(Activities(u,2),Activities(1,2));
            else
                A(ineq,(v-1)*N^2+(u-1)*N+w)=Net_Time(Activities(u,2),Activities(w,2));
            end
        end
    end
end

%constraint (21)
for v=1:Vehicles
    Aeq=[Aeq; zeros(1,numVar)];
    beq=[beq; 0];
    ieq=ieq+1;
    Aeq(ieq,(v-1)*N^2+Pplus+1+1:(v-1)*N^2+Pplus+1+Pplus)=1;
end

%constraint (22)
for v=1:Vehicles
    Aeq=[Aeq; zeros(1,numVar)];
    beq=[beq; 0];
    ieq=ieq+1;
    for u=1:N
        Aeq(ieq,(v-1)*N^2+(u-1)*N+1)=1;
    end
end

%constraint (23)
for v=1:Vehicles
    Aeq=[Aeq; zeros(1,numVar)];
    beq=[beq; 0];
    ieq=ieq+1;
    for u=1:Pplus
        Aeq(ieq,(v-1)*N^2+u*N+N)=1;
    end
end

%constraint (24)
for v=1:Vehicles
    Aeq=[Aeq; zeros(1,numVar)];
    beq=[beq; 0];
    ieq=ieq+1;
    Aeq(ieq,(v-1)*N^2+(N-1)*N+Pplus+1+1:(v-1)*N^2+(N-1)*N+Pplus+1+Pplus)=1;
end
            
%InvMILP Solver - need to modify to make it work for VRP objective
%coefficients
%these setup the HAPP model as the numVar + 6 additional dummy variables
%for each objective, zeroing out the weight of all the other variables in
%obj
n=numVar+5+Vehicles+2*Pplus;

A=[A zeros(ineq,5+Vehicles+2*Pplus)];  %the 2x Pplus is for tracking early and late arrivals
Aeq=[Aeq zeros(ieq,5+Vehicles+2*Pplus)];
lb=[lb zeros(1,5+Vehicles+2*Pplus)];
lb(1,numVar+3:numVar+4)=-inf;
ub=[ub inf+zeros(1,5+Vehicles+2*Pplus)];

wprime=[zeros(numVar,1); weight];
cprime=[zeros(numVar,1); c];
S=[];
stop=0;
numiter=0

%this is to reformulate the HAPP model with 
%obj 1a
Aeq=[Aeq; zeros(1,n)];
beq=[beq; 0];
ieq=ieq+1;
for v=1:Vehicles
    for u=1:N
        for w=1:N
            if and(u>Pplus+1,w>Pplus+1)
                Aeq(ieq,(v-1)*N^2+(u-1)*N+w)=Net_Cost(Activities(1,2),Activities(1,2));
            elseif and(u>Pplus+1,w<=Pplus+1)
                Aeq(ieq,(v-1)*N^2+(u-1)*N+w)=Net_Cost(Activities(1,2),Activities(w,2));
            elseif and(u<=Pplus+1,w>Pplus+1)
                Aeq(ieq,(v-1)*N^2+(u-1)*N+w)=Net_Cost(Activities(u,2),Activities(1,2));
            else
                Aeq(ieq,(v-1)*N^2+(u-1)*N+w)=Net_Cost(Activities(u,2),Activities(w,2));
            end
        end
    end
end
Aeq(ieq,numVar+1)=-1;
C(1,1)=Aeq(ieq,1:numVar)*[X;T;Y];

%obj 1b
Aeq=[Aeq; zeros(1,n)];
beq=[beq; 0];
ieq=ieq+1;
for v=1:Vehicles
    for u=1:N
        for w=1:N
            if and(u>Pplus+1,w>Pplus+1)
                Aeq(ieq,(v-1)*N^2+(u-1)*N+w)=Net_Time(Activities(1,2),Activities(1,2));
            elseif and(u>Pplus+1,w<=Pplus+1)
                Aeq(ieq,(v-1)*N^2+(u-1)*N+w)=Net_Time(Activities(1,2),Activities(w,2));
            elseif and(u<=Pplus+1,w>Pplus+1)
                Aeq(ieq,(v-1)*N^2+(u-1)*N+w)=Net_Time(Activities(u,2),Activities(1,2));
            else
                Aeq(ieq,(v-1)*N^2+(u-1)*N+w)=Net_Time(Activities(u,2),Activities(w,2));
            end
        end
    end
end
Aeq(ieq,numVar+2)=-1;
C(2,1)=Aeq(ieq,1:numVar)*[X;T;Y];

%obj 1c
Aeq=[Aeq; zeros(1,n)];
beq=[beq; 0];
ieq=ieq+1;
for u=1:Pplus
    Aeq(ieq,Vehicles*N*N+u)=1;
    beq(ieq,1)=beq(ieq,1)+Activities(u+1,5);
end
Aeq(ieq,numVar+3)=-1;
C(3,1)=Aeq(ieq,1:numVar)*[X;T;Y]-beq(ieq,1);

%obj 1d
Aeq=[Aeq; zeros(1,n)];
beq=[beq; 0];
ieq=ieq+1;
for u=1:Pplus
    Aeq(ieq,Vehicles*N^2+Pplus+u)=1;
    beq(ieq,1)=beq(ieq,1)+Activities(u+1,7);
end
Aeq(ieq,numVar+4)=-1;
C(4,1)=Aeq(ieq,1:numVar)*[X;T;Y]-beq(ieq,1);

%obj 1e
Aeq=[Aeq; zeros(1,n)];
beq=[beq; 0];
ieq=ieq+1;
for u=1:Pplus
    Aeq(ieq,Vehicles*N*N+u+Pplus)=1;
    Aeq(ieq,Vehicles*N*N+u)=-1;
end
Aeq(ieq,numVar+5)=-1;
C(5,1)=Aeq(ieq,1:numVar)*[X;T;Y];

%obj 1f
for v=1:Vehicles
    Aeq=[Aeq; zeros(1,n)];
    beq=[beq; 0];
    ieq=ieq+1;
    Aeq(ieq,Vehicles*N^2+N-2+v)=-1;
    Aeq(ieq,Vehicles*N^2+N-2+Vehicles+v)=1;
    Aeq(ieq,numVar+5+v)=-1;
    C(5+v,1)=Aeq(ieq,1:numVar)*[X;T;Y];
end

Pe=zeros(Pplus,1);
Pl=Pe;
bf=zeros(2*ieq+ineq+2*Pplus,Pplus);

%soft time window constraints
for u=1:Pplus
    %less than arrival (late arrival)
    A=[A; zeros(1,n)];
    b=[b; 0];
    ineq=ineq+1;
    A(ineq,Vehicles*N^2+u)=1;
    A(ineq,numVar+5+Vehicles+u)=1;
    A(ineq,numVar+5+Vehicles+Pplus+u)=-1;
    bf(2*ieq+ineq,u)=-1;    %12/29/11 - fixed
    Pl(u,1)=max(0,T(u,1)-Activities(u+1,4));
    %greater than arrival (early arrival)
    A=[A; zeros(1,n)];
    b=[b; 0];
    ineq=ineq+1;
    A(ineq,Vehicles*N^2+u)=-1;
    A(ineq,numVar+5+Vehicles+u)=-1;
    A(ineq,numVar+5+Vehicles+Pplus+u)=1;
    bf(2*ieq+ineq,u)=1;     %12/29/11 - fixed
    Pe(u,1)=max(0,Activities(u+1,4)-T(u,1));
end
    
%construct Aprime the combined
Aprime=[Aeq; -Aeq; A];      %12/29/11 - fixed
%construct corresponding bprime
bprime=[beq; -beq; b];

XTYC=[X;T;Y;C];
m=size(bprime,1);

w2prime=ones(2*Pplus,1); %early e, late e, early f, late f

%define fprime as the objective function (12) from Wang
fprime=[wprime;wprime;w2prime;w2prime;zeros(Pplus,1);zeros(m,1)];
efyn=size(fprime,1);
%define the constraints for the LP solver
Aprime1=[[-eye(n-2*Pplus);zeros(2*Pplus,n-2*Pplus)] [eye(n-2*Pplus);zeros(2*Pplus,n-2*Pplus)] zeros(n,4*Pplus) zeros(n,Pplus) -Aprime'];
bprime1=[-cprime; .613*ones(Pplus,1); 2.396*ones(Pplus,1)];

for u=1:Pplus
    Aprime1=[Aprime1;zeros(1,n-2*Pplus) zeros(1,n-2*Pplus) zeros(1,u-1) 1 zeros(1,Pplus-u) zeros(1,u-1) -1 zeros(1,Pplus-u) zeros(1,u-1) -1 zeros(1,Pplus-u) zeros(1,u-1) 1 zeros(1,Pplus-u) zeros(1,u-1) 1 zeros(1,Pplus-u) zeros(1,m)];
    Aprime1=[Aprime1;zeros(1,n-2*Pplus) zeros(1,n-2*Pplus) zeros(1,u-1) -1 zeros(1,Pplus-u) zeros(1,u-1) 1 zeros(1,Pplus-u) zeros(1,u-1) 1 zeros(1,Pplus-u) zeros(1,u-1) -1 zeros(1,Pplus-u) zeros(1,u-1) -1 zeros(1,Pplus-u) zeros(1,m)];
    %for the nonnegativity constraints: Pe - ee2 + fe2 >=0, Pl - el2 + fl2
    %>=0
    Aprime1=[Aprime1;zeros(1,n-2*Pplus) zeros(1,n-2*Pplus) zeros(1,u-1) 1 zeros(1,Pplus-u) zeros(1,Pplus) zeros(1,u-1) -1 zeros(1,Pplus-u) zeros(1,Pplus) zeros(1,Pplus) zeros(1,m)];
    Aprime1=[Aprime1;zeros(1,n-2*Pplus) zeros(1,n-2*Pplus) zeros(1,Pplus) zeros(1,u-1) 1 zeros(1,Pplus-u) zeros(1,Pplus) zeros(1,u-1) -1 zeros(1,Pplus-u) zeros(1,Pplus) zeros(1,m)];
    bprime1=[bprime1; T(u,1)+Pe(u,1)-Pl(u,1); -T(u,1)-Pe(u,1)+Pl(u,1)];
    bprime1=[bprime1; Pe(u,1); Pl(u,1)];
end
   
BinaryArray=[];
for i=1:Vehicles*N^2
    BinaryArray=[BinaryArray 'B'];
end
ContArray=[];
for i=1:n-Vehicles*N^2
    ContArray=[ContArray 'C'];
end
efynub=zeros(efyn,1);
for i=numVar+1:n-2*Pplus
    if wprime(i,1)~=0
        efynub(i,1)=inf;
        efynub(i+n-2*Pplus,1)=inf;
    end
end
efynub(2*(n-2*Pplus)+1:efyn,1)=inf;
    
while and(stop==0,numiter<500)
    %this is the plane cutting portion
    numS=size(S,2);
    if numS>0
        Aprime1=[Aprime1; (XTYC-S(1:n-2*Pplus,numS))' (S(1:n-2*Pplus,numS)-XTYC)' -0.613*ones(1,Pplus) -2.396*ones(1,Pplus) 0.613*ones(1,Pplus) 2.396*ones(1,Pplus) zeros(1,Pplus) zeros(1,m)]; %trying out less than ineq, JC 8/14/10
        bprime1=[bprime1; cprime'*(XTYC-S(1:n-2*Pplus,numS))+(-0.613*ones(Pplus,1))'*(Pe-S(n-2*Pplus+1:n-2*Pplus+Pplus,numS))+(-2.396*ones(Pplus,1))'*(Pl-S(n-2*Pplus+Pplus+1:n,numS))];
    end

    [xsol,~,~]=cplexlp(fprime,Aprime1,bprime1,[],[],zeros(efyn,1),efynub);
    
    e1=xsol(1:n-2*Pplus,1);
    f1=xsol(n-2*Pplus+1:2*(n-2*Pplus),1);
    e2=xsol(2*(n-2*Pplus)+1:2*(n-2*Pplus)+2*Pplus,1);
    f2=xsol(2*(n-2*Pplus)+2*Pplus+1:2*(n-2*Pplus)+2*Pplus+2*Pplus,1);
    Arrivals=xsol(2*(n-2*Pplus)+4*Pplus+1:2*(n-2*Pplus)+4*Pplus+Pplus,1);
    y=xsol(2*(n-2*Pplus)+5*Pplus+1:2*(n-2*Pplus)+5*Pplus+m,1);
    d=cprime-e1+f1;
    XTYCP=[XTYC;Pe-e2(1:Pplus,1)+f2(1:Pplus,1);Pl-e2(Pplus+1:2*Pplus,1)+f2(Pplus+1:2*Pplus,1)];
    
    [x1,fval,exitflag]=cplexmilp([-d;.613*ones(Pplus,1);2.396*ones(Pplus,1)],Aprime,bprime-bf*Arrivals,[],[],[],[],[],lb',ub',[BinaryArray ContArray]);
    if numiter==0
        check=zeros(size(d,1)+2*Pplus,1);
    else
        check=S(:,size(S,2));
    end
    if or([d;-.613*ones(Pplus,1);-2.396*ones(Pplus,1)]'*XTYCP>=[d;-.613*ones(Pplus,1);-2.396*ones(Pplus,1)]'*x1,x1==check)      %9-22-10 adding a new condition
        stop=1;
        if and([d;-.613*ones(Pplus,1);-2.396*ones(Pplus,1)]'*XTYCP<[d;-.613*ones(Pplus,1);-2.396*ones(Pplus,1)]'*x1,x1==check)
            exitflag=0;
        end
    else
        S=[S x1];
    end
    numiter=numiter+1
end
Objectives=-d(numVar+1:n-2*Pplus,1);

%check to see if input x is feasible
if min(Aprime*XTYCP<=bprime-bf*Arrivals)==0
    exitflag=-1;  %for infeasible value
end
if numiter==500
    exitflag=-2;
end




