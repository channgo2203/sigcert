process P=
(? integer FB1,FB2; boolean b init true;
 ! integer N;)
 (| N := (FB1 when b) default FB2
  | ZN := N$1 init 0
  |)
