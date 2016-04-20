process P=
(? integer FB1, FB2; integer FB3; boolean Co init true;
 ! integer N;)
pragmas
pra1 {object1 object2}
pra1 {object1 object2} "pra1"
end pragmas
(| x := y + 1
 | N := FB1 when FB2 >= 1
 | FB3 := 1 + N$1 + 4*3
 | De := 3*N$1 init 4*9
 | Celltest := FB cell FB1$1 init true
 | ZN := when not FB1 + 2 <= 1
 | x ^= y ^= z
 | (| o := i + 1
    | (| o1 := i + 2 |)/ o1
    |)/ o
 |)
 where
	integer ZN init 3*6; boolean b init false;
	type my_int = integer;
	process P0=
	(? real r;
	 ! real ro)
	(| ro := r * 9 + P00(r) + P01(r)
	 |)
	 where
	 	process P00=
		(? real i;
		 ! real o)
		(| o := i + 1
		 |);
		process P01=
		(? real in;
		 ! real out)
		(| out := in * 2 + 1
		 |)
	 end;
	process P1=
	(? real i1;
	 ! real o1)
	(| o1 := i1 + 2 * 3
	 |)
 end;

