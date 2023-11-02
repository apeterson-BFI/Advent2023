From Coq Require Import String.
From Coq Require Import Ascii.
From Coq Require Import Arith.
From Coq Require Import NArith.
From Coq Require Import NArith.BinNat.
From Coq Require Import Lists.List.
Require Import day1.
Import ListNotations.

Definition inp2 := 
  ["798	1976	1866	1862	559	1797	1129	747	85	1108	104	2000	248	131	87	95"%string;
    "201	419	336	65	208	57	74	433	68	360	390	412	355	209	330	135"%string;
    "967	84	492	1425	1502	1324	1268	1113	1259	81	310	1360	773	69	68	290"%string;
    "169	264	107	298	38	149	56	126	276	45	305	403	89	179	394	172"%string;
    "3069	387	2914	2748	1294	1143	3099	152	2867	3082	113	145	2827	2545	134	469"%string;
    "3885	1098	2638	5806	4655	4787	186	4024	2286	5585	5590	215	5336	2738	218	266"%string;
    "661	789	393	159	172	355	820	891	196	831	345	784	65	971	396	234"%string;
    "4095	191	4333	161	3184	193	4830	4153	2070	3759	1207	3222	185	176	2914	4152"%string;
    "131	298	279	304	118	135	300	74	269	96	366	341	139	159	17	149"%string;
    "1155	5131	373	136	103	5168	3424	5126	122	5046	4315	126	236	4668	4595	4959"%string;
    "664	635	588	673	354	656	70	86	211	139	95	40	84	413	618	31"%string;
    "2163	127	957	2500	2370	2344	2224	1432	125	1984	2392	379	2292	98	456	154"%string;
    "271	4026	2960	6444	2896	228	819	676	6612	6987	265	2231	2565	6603	207	6236"%string;
    "91	683	1736	1998	1960	1727	84	1992	1072	1588	1768	74	58	1956	1627	893"%string;
    "3591	1843	3448	1775	3564	2632	1002	3065	77	3579	78	99	1668	98	2963	3553"%string;
    "2155	225	2856	3061	105	204	1269	171	2505	2852	977	1377	181	1856	2952	2262"%string].

Definition exa21 := 
  ["5 1 9 5"%string;
   "7 5 3"%string;
   "2 4 6 8"%string].

Definition exa22 :=
  ["22 1 5"%string;
   "100 15 2"%string;
   "80 10 12"%string].

Definition exa23 :=
  ["5 9 2 8"%string;
   "9 4 7 3"%string;
   "3 8 6 5"%string].

Local Open Scope N_scope.

Fixpoint getListNumWS (builder : N)  (s : string) :=
  match s with
  | EmptyString => [ builder ]
  | String a s' =>
    if (N_of_ascii a) <? 48
    then
      if builder =? 0 
      then getListNumWS 0 s'
      else builder :: (getListNumWS 0 s')
    else
      getListNumWS (builder * 10 + (N_of_ascii a) - 48) s'
  end.

Definition getNumberGridWS (slist : list string) :=
  map (getListNumWS 0) slist.

Definition extremediff (nlist : list N) :=
  let mx := fold_right N.max 0 nlist in
  let mi := fold_right N.min 1000000 nlist in
  mx - mi.

Definition day2p1 (slist : list string) :=
  let numGD := getNumberGridWS slist in
  let md := map extremediff numGD in
  fold_right N.add 0 md.

Compute (day2p1 inp2).

Definition divo (nmt : N * N) :=
  match nmt with
  | (a,b) => 
    if a =? b
    then None
    else
      if (a mod b) =? 0
      then Some (a / b)
      else None
  end.

Definition optl (no : option N) (mo : option N) :=
  match no,mo with
  | None, None => None
  | None, Some m => Some m
  | Some n, None => Some n
  | Some n, Some m => Some n
  end.

Definition optsum (no : option N) (mo : option N) :=
  match no,mo with
  | None, None => None
  | None, Some m => Some m
  | Some n, None => Some n
  | Some n, Some m => Some (n + m)
  end.

Definition onlydiv (nlist : list N) :=
  let fm1 := flat_map (fun n => map (fun o => (n,o)) nlist) nlist in
  let fm2 := map divo fm1 in
  fold_right optl None fm2.

Definition day2p2 (slist : list string) :=
  let numGD := getNumberGridWS slist in
  let cp := flat_map (fun nl => flat_map (fun n => map (fun o => (n,o)) nl) nl) numGD in
  let mp := map divo cp in
  fold_right optsum (Some 0) mp.

Compute (day2p2 exa23).
Compute (day2p2 inp2).
  