import Mathlib
import Submission.Work.Main.defs
import Submission.Work.IntLib.chunksAPI
import Submission.Work.Main.bridge
import Submission.Work.Main.word.toCfx
import Submission.Work.MainP.crtDefs
import Submission.Work.Main.step.crtExtract
import Submission.Work.Main.step.cvecValSizePrep
import Submission.Work.Main.step.prepSizes

set_option autoImplicit false
set_option maxRecDepth 500000
set_option maxHeartbeats 12000000

namespace Work.Main.step

open HvdH

/-! ## Helpers for the `prep` stage -/

/-- The nine parameter values of `env sp R`, as an explicit list. -/
def env9 (sp : SP) : List Val :=
  [Val.int (sp.S : ℤ), Val.int (sp.N' : ℤ), Val.int (sp.b : ℤ), Val.int (sp.p : ℤ), Val.int (sp.α : ℤ),
    intList sp.ts, intList sp.ss, Val.int (sp.x : ℤ), Val.int (sp.y : ℤ)]

theorem env_eq_env9 (sp : SP) (R : List Val) : env sp R = env9 sp ++ R := rfl

theorem envsz_eq (sp : SP) : envsz sp = ((env9 sp).map vsz).sum := by
  simp [envsz, env_eq_env9]

theorem env9_length (sp : SP) : (env9 sp).length = 9 := rfl

/-- `env sp R` reads its nine parameters. -/
theorem env_getD0 (sp : SP) (R : List Val) : (env sp R).getD 0 .nil = Val.int (sp.S : ℤ) := by
  simp [env_eq_env9, env9]
theorem env_getD1 (sp : SP) (R : List Val) : (env sp R).getD 1 .nil = Val.int (sp.N' : ℤ) := by
  simp [env_eq_env9, env9]
theorem env_getD2 (sp : SP) (R : List Val) : (env sp R).getD 2 .nil = Val.int (sp.b : ℤ) := by
  simp [env_eq_env9, env9]
theorem env_getD3 (sp : SP) (R : List Val) : (env sp R).getD 3 .nil = Val.int (sp.p : ℤ) := by
  simp [env_eq_env9, env9]
theorem env_getD4 (sp : SP) (R : List Val) : (env sp R).getD 4 .nil = Val.int (sp.α : ℤ) := by
  simp [env_eq_env9, env9]
theorem env_getD5 (sp : SP) (R : List Val) : (env sp R).getD 5 .nil = intList sp.ts := by
  simp [env_eq_env9, env9]
theorem env_getD6 (sp : SP) (R : List Val) : (env sp R).getD 6 .nil = intList sp.ss := by
  simp [env_eq_env9, env9]
theorem env_getD7 (sp : SP) (R : List Val) : (env sp R).getD 7 .nil = Val.int (sp.x : ℤ) := by
  simp [env_eq_env9, env9]
theorem env_getD8 (sp : SP) (R : List Val) : (env sp R).getD 8 .nil = Val.int (sp.y : ℤ) := by
  simp [env_eq_env9, env9]

theorem le_sum_of_mem {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons b t ih =>
      rw [List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · have := ih h; simp; omega

theorem sum_map_take_le (l : List Val) (n : ℕ) :
    ((l.take n).map vsz).sum ≤ (l.map vsz).sum := by
  induction l generalizing n with
  | nil => simp
  | cons a t ih =>
      cases n with
      | zero => simp
      | succ n =>
          rw [List.take_succ_cons, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
          exact Nat.add_le_add_left (ih n) _

theorem map_sum_le_of_forall {l : List Val} {c : ℕ} (h : ∀ v ∈ l, vsz v ≤ c) :
    (l.map vsz).sum ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.map_cons, List.sum_cons, List.length_cons]
      have ha : vsz a ≤ c := h a (by simp)
      have ht : (t.map vsz).sum ≤ t.length * c := ih (fun v hv => h v (by simp [hv]))
      calc vsz a + (t.map vsz).sum ≤ c + t.length * c := Nat.add_le_add ha ht
        _ = (t.length + 1) * c := by ring

theorem map_sum_le_card {l : List Val} {c k : ℕ} (hlen : l.length ≤ k)
    (h : ∀ v ∈ l, vsz v ≤ c) : (l.map vsz).sum ≤ k * c :=
  le_trans (map_sum_le_of_forall h) (Nat.mul_le_mul_right _ hlen)

theorem take_env_le (sp : SP) (R : List Val) (m : ℕ) (hm : m ≤ 9) :
    (((env sp R).take m).map vsz).sum ≤ envsz sp := by
  have h9m : m ≤ (env9 sp).length := by rw [env9_length]; exact hm
  have htake : (env sp R).take m = (env9 sp).take m := by
    rw [env_eq_env9, List.take_append, Nat.sub_eq_zero_of_le h9m, List.take_zero, List.append_nil]
  rw [htake, envsz_eq]
  exact sum_map_take_le (env9 sp) m

theorem take_block_env_le {sp : SP} {X : List Val} {R : List Val} {n : ℕ}
    (hn : n ≤ X.length + 9) :
    (((X ++ env sp R).take n).map vsz).sum ≤ (X.map vsz).sum + envsz sp := by
  rw [List.take_append, List.map_append, List.sum_append]
  exact Nat.add_le_add (sum_map_take_le X n) (take_env_le sp R (n - X.length) (by omega))

theorem step_ht {sp : SP} {X : List Val} {R : List Val} {n Big : ℕ}
    (hn : n ≤ X.length + 9) (hX : (X.map vsz).sum ≤ 12 * Big) (hE : envsz sp ≤ Big)
    (hB1 : 1 ≤ Big) :
    (((X ++ env sp R).take n).map vsz).sum + 1 ≤ 33 * Big := by
  have h2 := take_block_env_le (sp := sp) (X := X) (R := R) (n := n) hn
  omega

theorem vsz_le_envsz {sp : SP} {v : Val} (h : v ∈ env9 sp) : vsz v ≤ envsz sp := by
  rw [envsz_eq]
  exact le_sum_of_mem (by rw [List.mem_map]; exact ⟨v, h, rfl⟩)

theorem chunks_lt (x b S : ℕ) : ∀ n ∈ HvdH.chunks x b S, n < 2 ^ b := by
  intro n hn
  rw [HvdH.chunks] at hn
  rcases List.mem_map.mp hn with ⟨j, -, rfl⟩
  exact Nat.mod_lt _ (Nat.pow_pos (by norm_num))

/-! ## Composition and exact-state wrappers for the library words -/

theorem seqE (hKer : KernelLib) {main p q : Cmd} {A B D : List Val} {c₁ c₂ : ℕ}
    (h1 : WordR main p (fun vs => vs = A) (fun _ out => out = B) (fun _ => c₁))
    (h2 : WordR main q (fun vs => vs = B) (fun _ out => out = D) (fun _ => c₂)) :
    WordR main (.seq p q) (fun vs => vs = A) (fun _ out => out = D) (fun _ => c₁ + c₂) := by
  have h := hKer.seq main p q (fun vs => vs = A) (fun _ out => out = B) (fun _ => c₁)
      (fun vs => vs = B) (fun _ out => out = D) (fun _ => c₂) (fun _ => c₂) h1 h2
      (fun vs mid ha hb => ⟨hb, le_rfl⟩)
  intro vs hv s R hs
  obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ := h vs hv s R hs
  obtain ⟨mid, hmid, hout⟩ := hpost
  exact ⟨out, s', n, hout, hev, hn, hstk, hfr⟩

theorem pickEx (hKer : KernelLib) {main : Cmd} {pickP : ℕ → Cmd} {Kpick : ℕ}
    (hpick : ∀ (main : Cmd) (k : ℕ), WordR main (pickP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => Kpick * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (k : ℕ) (l : List Val) (v : Val) (t c : ℕ)
    (hk : k < l.length) (hv : l.getD k .nil = v)
    (ht : ((l.take (k + 1)).map vsz).sum + 1 ≤ t) (hc : Kpick * (k + 1) * t ≤ c) :
    WordR main (pickP k) (fun vs => vs = l) (fun _ out => out = v :: l) (fun _ => c) := by
  intro vs hvs s R hs
  obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ :=
    hpick main k vs (by rw [hvs]; exact hk) s R hs
  refine ⟨out, s', n, ?_, hev, ?_, hstk, hfr⟩
  · rw [hpost, hvs, hv]
  · rw [hvs] at hn
    exact le_trans hn (le_trans (Nat.mul_le_mul_left _ ht) hc)

theorem rollEx (hKer : KernelLib) {main : Cmd} {rollP : ℕ → Cmd} {Kroll : ℕ}
    (hroll : ∀ (main : Cmd) (k : ℕ), WordR main (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => Kroll * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (k : ℕ) (l l' : List Val) (t c : ℕ)
    (hk : k < l.length) (hv : l.getD k .nil :: l.eraseIdx k = l')
    (ht : ((l.take (k + 1)).map vsz).sum + 1 ≤ t) (hc : Kroll * (k + 1) * t ≤ c) :
    WordR main (rollP k) (fun vs => vs = l) (fun _ out => out = l') (fun _ => c) := by
  intro vs hvs s R hs
  obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ :=
    hroll main k vs (by rw [hvs]; exact hk) s R hs
  refine ⟨out, s', n, ?_, hev, ?_, hstk, hfr⟩
  · rw [hpost, hvs, hv]
  · rw [hvs] at hn
    exact le_trans hn (le_trans (Nat.mul_le_mul_left _ ht) hc)

theorem swapEx (hKer : KernelLib) {main : Cmd} {swapP : Cmd} {Kswap : ℕ}
    (hswap : ∀ main, WordR main swapP (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => Kswap * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    (a b : Val) (rest : List Val) (t c : ℕ)
    (ht : vsz a + vsz b + 1 ≤ t) (hc : Kswap * t ≤ c) :
    WordR main swapP (fun vs => vs = a :: b :: rest) (fun _ out => out = b :: a :: rest)
      (fun _ => c) := by
  intro vs hvs s R hs
  obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ :=
    hswap main vs (by rw [hvs]; simp) s R hs
  obtain ⟨a', b', r', hab, hout⟩ := hpost
  rw [hvs] at hab
  simp only [List.cons.injEq] at hab
  obtain ⟨h1, h2, h3⟩ := hab
  subst h1; subst h2; subst h3
  refine ⟨out, s', n, hout, hev, ?_, hstk, hfr⟩
  have e1 : (a :: b :: rest).getD 0 .nil = a := rfl
  have e2 : (a :: b :: rest).getD 1 .nil = b := rfl
  rw [hvs] at hn
  change n ≤ Kswap * (vsz ((a :: b :: rest).getD 0 .nil)
    + vsz ((a :: b :: rest).getD 1 .nil) + 1) at hn
  rw [e1, e2] at hn
  exact le_trans hn (le_trans (Nat.mul_le_mul_left _ ht) hc)

theorem pushValEx (hKer : KernelLib) {main : Cmd} {pushP : Val → Cmd} {Kpush : ℕ}
    (hpush : ∀ (main : Cmd) (v : Val), WordR main (pushP v) (fun _ => True)
      (fun vs out => out = v :: vs) (fun _ => Kpush * (vsz v + 1)))
    (v : Val) (rest : List Val) (c : ℕ) (hc : Kpush * (vsz v + 1) ≤ c) :
    WordR main (pushP v) (fun vs => vs = rest) (fun _ out => out = v :: rest) (fun _ => c) := by
  intro vs hvs s R hs
  obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ :=
    hpush main v vs trivial s R hs
  refine ⟨out, s', n, ?_, hev, le_trans hn hc, hstk, hfr⟩
  rw [hpost, hvs]

theorem dropEx (hKer : KernelLib) {main : Cmd} {dropP : Cmd} {Kdrop : ℕ}
    (hdrop : ∀ (main : Cmd), WordR main dropP (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => Kdrop * (vsz (vs.headD .nil) + 1)))
    (a : Val) (rest : List Val) (c : ℕ) (hc : Kdrop * (vsz a + 1) ≤ c) :
    WordR main dropP (fun vs => vs = a :: rest) (fun _ out => out = rest) (fun _ => c) := by
  intro vs hvs s R hs
  obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ :=
    hdrop main vs (by rw [hvs]; simp) s R hs
  obtain ⟨v, r', hab, hout⟩ := hpost
  rw [hvs] at hab
  simp only [List.cons.injEq] at hab
  obtain ⟨h1, h2⟩ := hab
  subst h1; subst h2
  refine ⟨out, s', n, hout, hev, ?_, hstk, hfr⟩
  have e1 : (a :: rest).headD .nil = a := rfl
  rw [hvs] at hn
  change n ≤ Kdrop * (vsz ((a :: rest).headD .nil) + 1) at hn
  rw [e1] at hn
  exact le_trans hn hc

theorem chunkEx {main : Cmd} {chunkP : Cmd} {Kch : ℕ}
    (hchunk : ∀ (main : Cmd) (x b N : ℕ), 1 ≤ b → x < 2 ^ (b * N) →
      WordR main chunkP (fun vs => ∃ rest, vs = .int (x : ℤ) :: .int (b : ℤ) :: .int (N : ℤ) :: rest)
        (fun vs out => ∃ rest, vs = .int (x : ℤ) :: .int (b : ℤ) :: .int (N : ℤ) :: rest ∧
          out = intList (HvdH.chunks x b N) :: rest)
        (fun _ => Kch * (isz (x : ℤ) + N * (b + 1) + isz (b : ℤ) + isz (N : ℤ))))
    (x b N : ℕ) (rest : List Val) (c : ℕ)
    (hb : 1 ≤ b) (hx : x < 2 ^ (b * N))
    (hc : Kch * (isz (x : ℤ) + N * (b + 1) + isz (b : ℤ) + isz (N : ℤ)) ≤ c) :
    WordR main chunkP (fun vs => vs = .int (x : ℤ) :: .int (b : ℤ) :: .int (N : ℤ) :: rest)
      (fun _ out => out = intList (HvdH.chunks x b N) :: rest) (fun _ => c) := by
  intro vs hvs s R hs
  obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ :=
    hchunk main x b N hb hx vs ⟨rest, by simp [hvs]⟩ s R hs
  obtain ⟨r', hab, hout⟩ := hpost
  rw [hvs] at hab
  simp only [List.cons.injEq] at hab
  obtain ⟨-, -, -, h4⟩ := hab
  refine ⟨out, s', n, ?_, hev, le_trans hn hc, hstk, hfr⟩
  rw [hout, h4]

theorem toCfxEx {main : Cmd} {toCfxP : Cmd} {Kto : ℕ}
    (hto : ∀ (main : Cmd) (p b : ℕ) (xs : List ℕ) (rest : List Val), b ≤ p → (∀ j ∈ xs, j < 2 ^ b) →
      WordR main toCfxP (fun vs => vs = intList xs :: .int (p : ℤ) :: .int (b : ℤ) :: rest)
        (fun vs out => (∃ (ws : List (ℤ × ℤ)), vs = intList xs :: .int (p : ℤ) :: .int (b : ℤ) :: rest ∧
          out = cvecVal ws :: .int (p : ℤ) :: .int (b : ℤ) :: rest ∧ ws.length = xs.length ∧
          InDiscVec p xs.length ws ∧
          ∀ j < xs.length, ws.getD j (0, 0) = (((xs.getD j 0 : ℕ) : ℤ) * 2 ^ (p - b), 0)))
        (fun _ => Kto * (xs.length + 1) * (p + 1) + Kto))
    (p b : ℕ) (xs : List ℕ) (rest : List Val) (c : ℕ)
    (hbp : b ≤ p) (hxs : ∀ j ∈ xs, j < 2 ^ b)
    (hc : Kto * (xs.length + 1) * (p + 1) + Kto ≤ c) :
    WordR main toCfxP (fun vs => vs = intList xs :: .int (p : ℤ) :: .int (b : ℤ) :: rest)
      (fun _ out => ∃ (ws : List (ℤ × ℤ)), out = cvecVal ws :: .int (p : ℤ) :: .int (b : ℤ) :: rest ∧
        ws.length = xs.length ∧
        ∀ j < xs.length, ws.getD j (0, 0) = (((xs.getD j 0 : ℕ) : ℤ) * 2 ^ (p - b), 0))
      (fun _ => c) := by
  intro vs hvs s R hs
  obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ :=
    hto main p b xs rest hbp hxs vs (by rw [hvs]) s R hs
  obtain ⟨ws, -, hout, hwl, -, hw⟩ := hpost
  exact ⟨out, s', n, ⟨ws, hout, hwl, hw⟩, hev, le_trans hn hc, hstk, hfr⟩

theorem crtEx {main : Cmd} {crtP : Cmd} {Kcrt : ℕ}
    (hcrt : ∀ (main : Cmd) (ss : List ℕ) (dir : ℕ) (xs : List Val), (∀ s ∈ ss, 1 ≤ s) →
      ss.Pairwise Nat.Coprime → xs.length = ss.prod → dir ≤ 1 →
      WordR main crtP (fun vs => ∃ rest, vs = .int (dir : ℤ) :: intList ss :: ofList xs :: rest)
        (fun vs out => ∃ rest ys, vs = .int (dir : ℤ) :: intList ss :: ofList xs :: rest ∧
          out = ofList ys :: rest ∧ ys.length = ss.prod ∧
          ∀ m < ss.prod, (dir = 0 → ys.getD (HvdH.crtIdx ss m) .nil = xs.getD m .nil) ∧
            (dir = 1 → ys.getD m .nil = xs.getD (HvdH.crtIdx ss m) .nil))
        (fun _ => Kcrt * (vsz (ofList xs) + ss.prod * (vsz (intList ss) + 1) + 1) * (ss.prod.size + 1)))
    (ss : List ℕ) (xs : List Val) (rest : List Val) (c : ℕ)
    (h1 : ∀ s ∈ ss, 1 ≤ s) (hcop : ss.Pairwise Nat.Coprime) (hxl : xs.length = ss.prod)
    (hc : Kcrt * (vsz (ofList xs) + ss.prod * (vsz (intList ss) + 1) + 1) * (ss.prod.size + 1) ≤ c) :
    WordR main crtP (fun vs => vs = .int (0 : ℤ) :: intList ss :: ofList xs :: rest)
      (fun _ out => ∃ ys, out = ofList ys :: rest ∧ ys.length = ss.prod ∧
        ∀ m < ss.prod, ys.getD (HvdH.crtIdx ss m) .nil = xs.getD m .nil) (fun _ => c) := by
  intro vs hvs s R hs
  obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ :=
    hcrt main ss 0 xs h1 hcop hxl (by norm_num) vs ⟨rest, by rw [hvs]; simp⟩ s R hs
  obtain ⟨r', ys, hab, hout, hyl, hget⟩ := hpost
  rw [hvs] at hab
  simp only [List.cons.injEq] at hab
  obtain ⟨-, -, -, h4⟩ := hab
  refine ⟨out, s', n, ⟨ys, ?_, hyl, ?_⟩, hev, le_trans hn hc, hstk, hfr⟩
  · rw [hout, h4]
  · intro m hm
    exact (hget m hm).1 rfl



/-- the scaled chunk value fed to the CRT reindexing -/
def scaledChunk (k : ℕ) (xs : List ℕ) (j : ℕ) : ℤ × ℤ :=
  ((((xs.getD j 0 : ℕ)) : ℤ) * 2 ^ k, (0 : ℤ))

/-! ## Arithmetic domination lemmas -/

theorem vsz_chunks_le (x b S : ℕ) : vsz (intList (HvdH.chunks x b S)) ≤ S * (b + 3) + 1 := by
  have h := psz_intList_le (HvdH.chunks x b S) b (fun n hn => Nat.size_le.mpr (chunks_lt x b S n hn))
  rwa [Work.IntLib.chunks_length] at h

theorem vsz_cvec_getD_le {zs : List (ℤ × ℤ)} {xs : List ℕ} {b p : ℕ}
    (hb : b ≤ p) (hxs : ∀ j ∈ xs, j < 2 ^ b) (hzl : zs.length = xs.length)
    (h : ∀ j < xs.length, zs.getD j (0,0) = ((((xs.getD j 0 : ℕ)) : ℤ) * 2 ^ (p - b), 0)) :
    vsz (cvecVal zs) ≤ zs.length * (2 * p + 6) + 1 := by
  apply psz_cvecVal_le
  intro z hz
  obtain ⟨j, hj, hjz⟩ := List.mem_iff_getElem.mp hz
  have hjx : j < xs.length := by rw [← hzl]; exact hj
  have hzj : z = ((((xs.getD j 0 : ℕ)) : ℤ) * 2 ^ (p - b), 0) := by
    rw [← hjz, ← List.getD_eq_getElem _ _ hj, h j hjx]
  have hxb : xs.getD j 0 ∈ xs := by
    rw [List.getD_eq_getElem _ _ hjx]; exact List.mem_iff_getElem.mpr ⟨j, hjx, rfl⟩
  rw [hzj]
  refine ⟨cvecValSize_isz_mul_pow_le (xs.getD j 0) b p hb (hxs _ hxb), ?_⟩
  have h2 : isz (0 : ℤ) = 2 := by simp [HvdH.isz]
  rw [h2]; omega

theorem dom_b3 {S p b z : ℕ} (hz : z ≤ S * (b + 3) + 1) :
    z ≤ 2 * ((S + 1) * (p + 1) * (b + 1) * (HvdH.D + 1)) := by
  rw [HvdH.D]
  have h2 : S * (b + 3) ≤ (S + 1) * (p + 1) * (b + 1) * (1729 + 1) := by
    have hb : b + 3 ≤ (b + 1) * ((p + 1) * (1729 + 1)) := by
      calc b + 3 ≤ 4 * (b + 1) := by omega
        _ = (b + 1) * 4 := by ring
        _ ≤ (b + 1) * ((p + 1) * (1729 + 1)) := Nat.mul_le_mul_left _ (by nlinarith [Nat.zero_le p])
    calc S * (b + 3) ≤ S * ((b + 1) * ((p + 1) * (1729 + 1))) := Nat.mul_le_mul_left _ hb
      _ ≤ (S + 1) * ((b + 1) * ((p + 1) * (1729 + 1))) := Nat.mul_le_mul_right _ (by omega)
      _ = (S + 1) * (p + 1) * (b + 1) * (1729 + 1) := by ring
  have h3 : 1 ≤ (S + 1) * (p + 1) * (b + 1) * (1729 + 1) := by
    calc (1 : ℕ) = 1 * 1 * 1 * 1 := by ring
      _ ≤ (S + 1) * (p + 1) * (b + 1) * (1729 + 1) := by gcongr <;> omega
  omega

theorem dom_2p6 {S p b z : ℕ} (hz : z ≤ S * (2 * p + 6) + 1) :
    z ≤ 2 * ((S + 1) * (p + 1) * (b + 1) * (HvdH.D + 1)) := by
  rw [HvdH.D]
  have h2 : S * (2 * p + 6) ≤ (S + 1) * (p + 1) * (b + 1) * (1729 + 1) := by
    have hb : 2 * p + 6 ≤ (p + 1) * ((b + 1) * (1729 + 1)) := by
      calc 2 * p + 6 ≤ 6 * (p + 1) := by omega
        _ = (p + 1) * 6 := by ring
        _ ≤ (p + 1) * ((b + 1) * (1729 + 1)) := Nat.mul_le_mul_left _ (by nlinarith [Nat.zero_le b])
    calc S * (2 * p + 6) ≤ S * ((p + 1) * ((b + 1) * (1729 + 1))) := Nat.mul_le_mul_left _ hb
      _ ≤ (S + 1) * ((p + 1) * ((b + 1) * (1729 + 1))) := Nat.mul_le_mul_right _ (by omega)
      _ = (S + 1) * (p + 1) * (b + 1) * (1729 + 1) := by ring
  have h3 : 1 ≤ (S + 1) * (p + 1) * (b + 1) * (1729 + 1) := by
    calc (1 : ℕ) = 1 * 1 * 1 * 1 := by ring
      _ ≤ (S + 1) * (p + 1) * (b + 1) * (1729 + 1) := by gcongr <;> omega
  omega

/-- The inner cost of the CRT word is dominated by ten times the first target term. -/
theorem crt_inner_le {S p b vszss vszts vszW szS : ℕ}
    (hW : vszW ≤ S * (2 * p + 6) + 1) (hb : 1 ≤ b) :
    (vszW + S * (vszss + 1) + 1) * szS
      ≤ 10 * ((S + 1) * (vszss + vszts + b + p + 1) * szS) := by
  have hX : p + 2 ≤ vszss + vszts + b + p + 1 := by omega
  have hX1 : 1 ≤ vszss + vszts + b + p + 1 := by omega
  have h1 : vszW * szS ≤ 8 * ((S + 1) * (vszss + vszts + b + p + 1) * szS) := by
    calc vszW * szS ≤ (S * (2 * p + 6) + 1) * szS := Nat.mul_le_mul_right _ hW
      _ ≤ ((S + 1) * (2 * p + 6)) * szS := by
            apply Nat.mul_le_mul_right
            nlinarith [Nat.zero_le S]
      _ = (S + 1) * (2 * p + 6) * szS := by ring
      _ ≤ (S + 1) * (8 * (vszss + vszts + b + p + 1)) * szS := by
            apply Nat.mul_le_mul_right
            apply Nat.mul_le_mul_left
            nlinarith [hX]
      _ = 8 * ((S + 1) * (vszss + vszts + b + p + 1) * szS) := by ring
  have h2 : S * (vszss + 1) * szS ≤ (S + 1) * (vszss + vszts + b + p + 1) * szS := by
    apply Nat.mul_le_mul_right
    calc S * (vszss + 1) ≤ (S + 1) * (vszss + 1) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ (S + 1) * (vszss + vszts + b + p + 1) := Nat.mul_le_mul_left _ (by omega)
  have h3 : 1 * szS ≤ (S + 1) * (vszss + vszts + b + p + 1) * szS := by
    apply Nat.mul_le_mul_right
    calc (1 : ℕ) = 1 * 1 := by ring
      _ ≤ (S + 1) * (vszss + vszts + b + p + 1) := by gcongr <;> omega
  rw [add_mul, add_mul]
  linarith


theorem bud_T {K T S₀ U : ℕ} (hU : U = 1000 * T * S₀) (hK : K ≤ S₀) : K * T ≤ U := by
  rw [hU]
  have h1 : K * T ≤ S₀ * T := Nat.mul_le_mul_right _ hK
  calc K * T ≤ S₀ * T := h1
    _ ≤ S₀ * T * 1000 := by
        calc S₀ * T = (S₀ * T) * 1 := (Nat.mul_one _).symm
          _ ≤ (S₀ * T) * 1000 := Nat.mul_le_mul_left _ (by norm_num)
    _ = 1000 * T * S₀ := by ring

theorem vsz_ofList_map_le {zs : List (ℤ × ℤ)} {xs : List ℕ} {b p : ℕ}
    (hb : b ≤ p) (hxs : ∀ j ∈ xs, j < 2 ^ b) (hzl : zs.length = xs.length)
    (h : ∀ j < xs.length, zs.getD j (0,0) = ((((xs.getD j 0 : ℕ)) : ℤ) * 2 ^ (p - b), 0)) :
    vsz (ofList (zs.map cfxVal)) ≤ zs.length * (2 * p + 6) + 1 := by
  have hpt : ∀ z ∈ zs, vsz (cfxVal z) ≤ 2 * p + 5 := by
    intro z hz
    obtain ⟨j, hj, hjz⟩ := List.mem_iff_getElem.mp hz
    have hjx : j < xs.length := by rw [← hzl]; exact hj
    have hzj : z = ((((xs.getD j 0 : ℕ)) : ℤ) * 2 ^ (p - b), 0) := by
      rw [← hjz, ← List.getD_eq_getElem _ _ hj, h j hjx]
    have hxb : xs.getD j 0 ∈ xs := by
      rw [List.getD_eq_getElem _ _ hjx]; exact List.mem_iff_getElem.mpr ⟨j, hjx, rfl⟩
    have h1 : isz ((((xs.getD j 0 : ℕ)) : ℤ) * 2 ^ (p - b)) ≤ p + 2 :=
      cvecValSize_isz_mul_pow_le (xs.getD j 0) b p hb (hxs _ hxb)
    have h2 : isz (0 : ℤ) = 2 := by simp [HvdH.isz]
    rw [hzj, psz_vsz_cfxVal]
    calc isz ((((xs.getD j 0 : ℕ)) : ℤ) * 2 ^ (p - b)) + isz (0 : ℤ) + 1
        ≤ (p + 2) + 2 + 1 := by
          have h3 : isz (0 : ℤ) ≤ 2 := le_of_eq h2
          exact Nat.add_le_add (Nat.add_le_add h1 h3) le_rfl
      _ ≤ 2 * p + 5 := by omega
  have hsum : ∀ (l : List (ℤ × ℤ)), (∀ z ∈ l, vsz (cfxVal z) ≤ 2 * p + 5) →
      ((l.map cfxVal).map vsz).sum ≤ l.length * (2 * p + 5) := by
    intro l hl
    induction l with
    | nil => simp
    | cons a t ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        have ha : vsz (cfxVal a) ≤ 2 * p + 5 := hl a (by simp)
        have ht : ((t.map cfxVal).map vsz).sum ≤ t.length * (2 * p + 5) :=
          ih (fun z hz => hl z (by simp [hz]))
        calc vsz (cfxVal a) + ((t.map cfxVal).map vsz).sum
            ≤ (2 * p + 5) + t.length * (2 * p + 5) := Nat.add_le_add ha ht
          _ = (t.length + 1) * (2 * p + 5) := by ring
  have hs : ((zs.map cfxVal).map vsz).sum ≤ zs.length * (2 * p + 5) := hsum zs hpt
  rw [psz_vsz_ofList, List.length_map]
  have hkey : zs.length * (2 * p + 6) = zs.length * (2 * p + 5) + zs.length := by ring
  rw [hkey]
  omega

/-! ## Budget helpers -/
/-- Bound for a `pick`/`roll` step with prefix bound `T` and unit cost `1000 * T * S₀`. -/
theorem bud_step' {K n T S₀ U : ℕ} (hU : U = 1000 * T * S₀) (hK : K ≤ S₀) (hn : n ≤ 1000) :
    K * n * T ≤ U := by
  rw [hU]
  have h1 : K * n ≤ S₀ * 1000 := by
    calc K * n ≤ S₀ * n := Nat.mul_le_mul_right _ hK
      _ ≤ S₀ * 1000 := Nat.mul_le_mul_left _ hn
  calc K * n * T = (K * n) * T := by ring
    _ ≤ (S₀ * 1000) * T := Nat.mul_le_mul_right _ h1
    _ = 1000 * T * S₀ := by ring

/-- Bound for a step whose inner cost is bounded by `1000 * T`. -/
theorem bud_big' {K X T S₀ U : ℕ} (hU : U = 1000 * T * S₀) (hK : K ≤ S₀) (hX : X ≤ 1000 * T) :
    K * X ≤ U := by
  rw [hU]
  calc K * X ≤ S₀ * X := Nat.mul_le_mul_right _ hK
    _ ≤ S₀ * (1000 * T) := Nat.mul_le_mul_left _ hX
    _ = 1000 * T * S₀ := by ring

/-- Bound for a step whose inner cost is bounded by `T`. -/
theorem bud_small' {K X T S₀ U : ℕ} (hU : U = 1000 * T * S₀) (hK : K ≤ S₀) (hX : X ≤ T) :
    K * X ≤ U := by
  rw [hU]
  calc K * X ≤ S₀ * X := Nat.mul_le_mul_right _ hK
    _ ≤ S₀ * T := Nat.mul_le_mul_left _ hX
    _ ≤ 1000 * T * S₀ := by
        calc S₀ * T = (S₀ * T) * 1 := (Nat.mul_one _).symm
          _ ≤ (S₀ * T) * 1000 := Nat.mul_le_mul_left _ (by norm_num)
          _ = 1000 * T * S₀ := by ring

/-- the `m`-th base-`2^b` chunk is the `pchunk` of the padded prefix -/
theorem chunks_getD_pchunk {x b N' S m : ℕ} (hN : N' ≤ S) (hx : x < 2 ^ (b * N')) (hm : m < S) :
    (HvdH.chunks x b S).getD m 0 = pchunk x b N' m := by
  rw [Work.IntLib.chunks_getD x b S m hm]
  unfold pchunk
  split_ifs with h
  · rfl
  · have hm' : N' ≤ m := Nat.le_of_not_lt h
    have hbm : b * N' ≤ b * m := Nat.mul_le_mul_left _ hm'
    have hx' : x < 2 ^ (b * m) := lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hbm)
    rw [Nat.div_eq_of_lt hx']
    simp
/-- the `m`-th scaled chunk equals the `pchunkZ` value used in the CRT-indexed vector -/
theorem scaledChunk_getD_pchunk {x b N' S k m : ℕ} (hN : N' ≤ S) (hx : x < 2 ^ (b * N')) (hm : m < S) :
    scaledChunk k (HvdH.chunks x b S) m = pchunkZ x b N' S k m := by
  unfold scaledChunk
  rw [chunks_getD_pchunk hN hx hm]
  simp only [pchunkZ, pchunkN]



theorem len_env (sp : SP) (R : List Val) : (env sp R).length = 9 + R.length := by
  rw [env_eq_env9, List.length_append, env9_length]

theorem len_block_of (sp : SP) (R : List Val) (X : List Val) :
    (X ++ env sp R).length = X.length + 9 + R.length := by
  rw [List.length_append, len_env]
  ring

/-- every prefix of a block of envinroment values costs at most `33 * B` -/
theorem step_ht' {sp : SP} {X : List Val} {R : List Val} {n Big : ℕ}
    (hn : n ≤ X.length + 9) (hX : (X.map vsz).sum ≤ 12 * Big) (hE : envsz sp ≤ Big)
    (hB1 : 1 ≤ Big) :
    (((X ++ env sp R).take n).map vsz).sum + 1 ≤ 33 * Big :=
  step_ht hn hX hE hB1

/-- Bound for a `pick`/`roll` step with prefix bound `33 * B` and unit cost. -/
theorem bud_step {K n B S₀ : ℕ} (hK : K ≤ S₀) (hn : n ≤ 1000) :
    K * n * (33 * B) ≤ 1000 * (33 * B) * S₀ := by
  have h1 : K * n ≤ S₀ * 1000 := by
    calc K * n ≤ S₀ * n := Nat.mul_le_mul_right _ hK
      _ ≤ S₀ * 1000 := Nat.mul_le_mul_left _ hn
  calc K * n * (33 * B) = (K * n) * (33 * B) := by ring
    _ ≤ (S₀ * 1000) * (33 * B) := Nat.mul_le_mul_right _ h1
    _ = 1000 * (33 * B) * S₀ := by ring

/-- Bound for a step whose inner cost is bounded by `1000 * (33 * B)`. -/
theorem bud_big {K X B S₀ : ℕ} (hK : K ≤ S₀) (hX : X ≤ 1000 * (33 * B)) :
    K * X ≤ 1000 * (33 * B) * S₀ := by
  calc K * X ≤ S₀ * X := Nat.mul_le_mul_right _ hK
    _ ≤ S₀ * (1000 * (33 * B)) := Nat.mul_le_mul_left _ hX
    _ = 1000 * (33 * B) * S₀ := by ring

/-- Bound for a step whose inner cost is bounded by `33 * B` (single value). -/
theorem bud_small {K X B S₀ : ℕ} (hK : K ≤ S₀) (hX : X ≤ 33 * B) :
    K * X ≤ 1000 * (33 * B) * S₀ := by
  calc K * X ≤ S₀ * X := Nat.mul_le_mul_right _ hK
    _ ≤ S₀ * (33 * B) := Nat.mul_le_mul_left _ hX
    _ ≤ 1000 * (33 * B) * S₀ := by
        calc S₀ * (33 * B) = (S₀ * (33 * B)) * 1 := (Nat.mul_one _).symm
          _ ≤ (S₀ * (33 * B)) * 1000 := Nat.mul_le_mul_left _ (by norm_num)
          _ = 1000 * (33 * B) * S₀ := by ring

/-- Bounded `chunks` entry. -/
theorem chunks_getD_lt (x b S j : ℕ) (hj : j < S) : (HvdH.chunks x b S).getD j 0 < 2 ^ b := by
  rw [Work.IntLib.chunks_getD x b S j hj]
  exact Nat.mod_lt _ (Nat.pow_pos (by norm_num))

theorem seqGen (hKer : KernelLib) {main p q : Cmd} {P Q S' : List Val → Prop} {c₁ c₂ : ℕ}
    (h1 : WordR main p P (fun _ out => Q out) (fun _ => c₁))
    (h2 : WordR main q Q (fun _ out => S' out) (fun _ => c₂)) :
    WordR main (.seq p q) P (fun _ out => S' out) (fun _ => c₁ + c₂) := by
  have h := hKer.seq main p q P (fun _ out => Q out) (fun _ => c₁) Q (fun _ out => S' out)
      (fun _ => c₂) (fun _ => c₂) h1 h2 (fun vs mid ha hb => ⟨hb, le_rfl⟩)
  intro vs hv s R hs
  obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ := h vs hv s R hs
  obtain ⟨mid, hmid, hout⟩ := hpost
  exact ⟨out, s', n, hout, hev, hn, hstk, hfr⟩


set_option maxHeartbeats 12000000
set_option maxRecDepth 500000

theorem prep (hKer : HvdH.KernelLib) (hInt : HvdH.IntLib) (hLay : HvdH.LayoutLib) (hC : HvdH.CrtWordProp) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (R : List HvdH.Val) (sp : SP),
      sp.x.size ≤ sp.b * sp.N' → sp.y.size ≤ sp.b * sp.N' → 1 ≤ sp.b → sp.b ≤ sp.p →
      sp.S = sp.ss.prod → sp.ss.length = HvdH.D → (∀ s ∈ sp.ss, 1 ≤ s) → sp.ss.Pairwise Nat.Coprime →
      sp.N' ≤ sp.S → sp.S ≤ 2 ^ sp.p →
      HvdH.WordR main prog
        (fun vs => vs = env sp R)
        (fun vs out => (∃ (F G : List (ℤ × ℤ)), vs = env sp R ∧
            out = HvdH.cvecVal F :: HvdH.cvecVal G :: env sp R ∧
            F.length = sp.S ∧ G.length = sp.S ∧
            (∀ m < sp.S, F.getD (HvdH.crtIdx sp.ss m) (0,0) = pchunkZ sp.x sp.b sp.N' sp.S (sp.p - sp.b) m) ∧
            (∀ m < sp.S, G.getD (HvdH.crtIdx sp.ss m) (0,0) = pchunkZ sp.y sp.b sp.N' sp.S (sp.p - sp.b) m)))
        (fun _ => K * (sp.S + 1) * (HvdH.vsz (HvdH.intList sp.ss) + HvdH.vsz (HvdH.intList sp.ts) + sp.b + sp.p + 1)
              * (sp.S.size + 1)
          + K * (sp.S + 1) * (sp.p + 1) * (sp.b + 1) * (HvdH.D + 1)
          + K * (sp.x.size + sp.y.size + sp.b + sp.N' + sp.S + 1)
          + K * (envsz sp + 1)) := by
  obtain ⟨pickP, Kpick, hpick⟩ := hKer.pick
  obtain ⟨rollP, Kroll, hroll⟩ := hKer.roll
  obtain ⟨swapP, Kswap, hswap⟩ := hKer.swap
  obtain ⟨pushP, Kpush, hpush⟩ := hKer.pushVal
  obtain ⟨dropP, Kdrop, hdrop⟩ := hKer.drop
  obtain ⟨chunkP, Kch, hchunk⟩ := hInt.chunk
  obtain ⟨toCfxP, Kto, hto⟩ := Work.Main.word.toCfx hKer hInt
  obtain ⟨crtP, Kcrt, hcrt⟩ := hC
  -- ---------- programs: stage 1 (argument y), stage 2 (argument x) ----------
  let yA8_7 : Cmd := rollP 2
  let yA8_6 : Cmd := .seq (rollP 1) yA8_7
  let yA8_5 : Cmd := .seq (pickP 4) yA8_6
  let yA8_4 : Cmd := .seq (pickP 4) yA8_5
  let yA8_3 : Cmd := .seq chunkP yA8_4
  let yA8_2 : Cmd := .seq (pickP 10) yA8_3
  let yA8_1 : Cmd := .seq (pickP 3) yA8_2
  let yA8 : Cmd := .seq (pickP 0) yA8_1
  let yD7 : Cmd := swapP
  let yD6 : Cmd := .seq (pickP 8) yD7
  let yD5 : Cmd := .seq (pushP (Val.int 0)) yD6
  let yD4 : Cmd := .seq dropP yD5
  let yD3 : Cmd := .seq (rollP 1) yD4
  let yD2 : Cmd := .seq dropP yD3
  let yD1 : Cmd := .seq (rollP 1) yD2
  let yC : Cmd := .seq yD1 crtP
  let yP : Cmd := .seq (.seq yA8 toCfxP) yC
  let xA8_7 : Cmd := rollP 2
  let xA8_6 : Cmd := .seq (rollP 1) xA8_7
  let xA8_5 : Cmd := .seq (pickP 5) xA8_6
  let xA8_4 : Cmd := .seq (pickP 5) xA8_5
  let xA8_3 : Cmd := .seq chunkP xA8_4
  let xA8_2 : Cmd := .seq (pickP 10) xA8_3
  let xA8_1 : Cmd := .seq (pickP 4) xA8_2
  let xA8 : Cmd := .seq (pickP 1) xA8_1
  let xD7 : Cmd := swapP
  let xD6 : Cmd := .seq (pickP 9) xD7
  let xD5 : Cmd := .seq (pushP (Val.int 0)) xD6
  let xD4 : Cmd := .seq dropP xD5
  let xD3 : Cmd := .seq (rollP 1) xD4
  let xD2 : Cmd := .seq dropP xD3
  let xD1 : Cmd := .seq (rollP 1) xD2
  let xC : Cmd := .seq xD1 crtP
  let xP : Cmd := .seq (.seq xA8 toCfxP) xC
  refine ⟨.seq yP xP, 1000000000 * (Kpick + Kroll + Kswap + Kpush + Kdrop + Kch + Kto + Kcrt + 1), ?_⟩
  intro main R sp hxsz hysz hb1 hbp hSp hDl hs1 hcop hNS hSpow
  set S₀ : ℕ := Kpick + Kroll + Kswap + Kpush + Kdrop + Kch + Kto + Kcrt + 1 with hS₀
  set Kprep : ℕ := 1000000000 * S₀ with hKprep
  set A1 : ℕ := (sp.S + 1) * (vsz (intList sp.ss) + vsz (intList sp.ts) + sp.b + sp.p + 1) * (sp.S.size + 1) with hA1
  set A2 : ℕ := (sp.S + 1) * (sp.p + 1) * (sp.b + 1) * (HvdH.D + 1) with hA2
  set A3 : ℕ := sp.x.size + sp.y.size + sp.b + sp.N' + sp.S + 1 with hA3
  set A4 : ℕ := envsz sp + 1 with hA4
  set Big : ℕ := A1 + A2 + A3 + A4 with hBig
  set T : ℕ := 100 * Big with hT
  set U : ℕ := 1000 * T * S₀ with hUeq
  have hKpick_le : Kpick ≤ S₀ := by rw [hS₀]; omega
  have hKroll_le : Kroll ≤ S₀ := by rw [hS₀]; omega
  have hKswap_le : Kswap ≤ S₀ := by rw [hS₀]; omega
  have hKpush_le : Kpush ≤ S₀ := by rw [hS₀]; omega
  have hKdrop_le : Kdrop ≤ S₀ := by rw [hS₀]; omega
  have hKch_le : Kch ≤ S₀ := by rw [hS₀]; omega
  have hKto_le : Kto ≤ S₀ := by rw [hS₀]; omega
  have hKcrt_le : Kcrt ≤ S₀ := by rw [hS₀]; omega
  have hBig1 : 1 ≤ Big := by rw [hBig, hA4]; omega
  have hEnvLe : envsz sp ≤ Big := by rw [hBig, hA4]; omega
  have hBig33 : 33 * Big ≤ T := by rw [hT]; omega
  have hA1le : A1 ≤ Big := by rw [hBig]; omega
  have hA2le : A2 ≤ Big := by rw [hBig]; omega
  have hA3le : A3 ≤ Big := by rw [hBig]; omega
  have hA4le : A4 ≤ Big := by rw [hBig]; omega
  have hS1 : 1 ≤ sp.S := by
    rw [hSp]
    have h := List.prod_pos (fun s hs => Nat.lt_of_lt_of_le Nat.zero_lt_one (hs1 s hs))
    omega
  have hp1 : 1 ≤ sp.p := le_trans hb1 hbp
  have hxpowN : sp.x < 2 ^ (sp.b * sp.N') :=
    lt_of_lt_of_le (Nat.lt_size_self sp.x) (Nat.pow_le_pow_right (by norm_num) hxsz)
  have hypowN : sp.y < 2 ^ (sp.b * sp.N') :=
    lt_of_lt_of_le (Nat.lt_size_self sp.y) (Nat.pow_le_pow_right (by norm_num) hysz)
  have hbN'S : sp.b * sp.N' ≤ sp.b * sp.S := Nat.mul_le_mul_left _ hNS
  have hxpowS : sp.x < 2 ^ (sp.b * sp.S) :=
    lt_of_lt_of_le hxpowN (Nat.pow_le_pow_right (by norm_num) hbN'S)
  have hypowS : sp.y < 2 ^ (sp.b * sp.S) :=
    lt_of_lt_of_le hypowN (Nat.pow_le_pow_right (by norm_num) hbN'S)
  have hmem : ∀ v ∈ env9 sp, vsz v ≤ Big := fun v hv => le_trans (vsz_le_envsz hv) hEnvLe
  have hbE : vsz (Val.int (sp.b : ℤ)) ≤ Big := hmem _ (by simp [env9])
  have hSE : vsz (Val.int (sp.S : ℤ)) ≤ Big := hmem _ (by simp [env9])
  have hNE : vsz (Val.int (sp.N' : ℤ)) ≤ Big := hmem _ (by simp [env9])
  have hpE : vsz (Val.int (sp.p : ℤ)) ≤ Big := hmem _ (by simp [env9])
  have hαE : vsz (Val.int (sp.α : ℤ)) ≤ Big := hmem _ (by simp [env9])
  have htsE : vsz (intList sp.ts) ≤ Big := hmem _ (by simp [env9])
  have hssE : vsz (intList sp.ss) ≤ Big := hmem _ (by simp [env9])
  have hxE : vsz (Val.int (sp.x : ℤ)) ≤ Big := hmem _ (by simp [env9])
  have hyE : vsz (Val.int (sp.y : ℤ)) ≤ Big := hmem _ (by simp [env9])
  have h0E : vsz (Val.int (0 : ℤ)) ≤ Big := by
    have h2 : vsz (Val.int (0 : ℤ)) = 2 := by simp [HvdH.isz, vsz_int]
    omega
  have hLx2 : sp.S * (2 * sp.p + 6) + 1 ≤ 2 * A2 := by
    have h := dom_2p6 (S := sp.S) (p := sp.p) (b := sp.b) (z := sp.S * (2 * sp.p + 6) + 1) le_rfl
    rw [hA2]; exact h
  have hLx3 : sp.S * (sp.b + 3) + 1 ≤ 2 * A2 := by
    have h := dom_b3 (S := sp.S) (p := sp.p) (b := sp.b) (z := sp.S * (sp.b + 3) + 1) le_rfl
    rw [hA2]; exact h
  have hLx : vsz (intList (HvdH.chunks sp.x sp.b sp.S)) ≤ 2 * Big := by
    have h1 := vsz_chunks_le sp.x sp.b sp.S
    have h3 : 2 * A2 ≤ 2 * Big := Nat.mul_le_mul_left _ hA2le
    omega
  have hLy : vsz (intList (HvdH.chunks sp.y sp.b sp.S)) ≤ 2 * Big := by
    have h1 := vsz_chunks_le sp.y sp.b sp.S
    have h3 : 2 * A2 ≤ 2 * Big := Nat.mul_le_mul_left _ hA2le
    omega
  -- ################ STAGE 1 (argument y) ################
  have hA1_0 : WordR main (pickP 0)
      (fun vs => vs = env sp R)
      (fun _ out => out = [Val.int (sp.S : ℤ)] ++ env sp R) (fun _ => U) :=
    pickEx hKer hpick 0 (env sp R) (Val.int (sp.S : ℤ)) T U
      (by simp only [List.length_append, List.length_cons, List.length_nil, len_env]; omega)
      (by simp [env_eq_env9, env9])
      (le_trans (step_ht (X := []) (n := 1) (by simp) (by simp) hEnvLe hBig1) hBig33)
      (bud_step' (T := T) (S₀ := S₀) (U := U) hUeq hKpick_le (by norm_num))
  have hA1_1 : WordR main (pickP 3)
      (fun vs => vs = [Val.int (sp.S : ℤ)] ++ env sp R)
      (fun _ out => out = [Val.int (sp.b : ℤ), Val.int (sp.S : ℤ)] ++ env sp R) (fun _ => U) :=
    pickEx hKer hpick 3 ([Val.int (sp.S : ℤ)] ++ env sp R) (Val.int (sp.b : ℤ)) T U
      (by simp only [List.length_append, List.length_cons, List.length_nil, len_env]; omega)
      (by simp [env_eq_env9, env9])
      (le_trans (step_ht (X := [Val.int (sp.S : ℤ)]) (n := 4) (by simp) (by simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]; omega) hEnvLe hBig1) hBig33)
      (bud_step' (T := T) (S₀ := S₀) (U := U) hUeq hKpick_le (by norm_num))
  have hA1_2 : WordR main (pickP 10)
      (fun vs => vs = [Val.int (sp.b : ℤ), Val.int (sp.S : ℤ)] ++ env sp R)
      (fun _ out => out = [Val.int (sp.y : ℤ), Val.int (sp.b : ℤ), Val.int (sp.S : ℤ)] ++ env sp R) (fun _ => U) :=
    pickEx hKer hpick 10 ([Val.int (sp.b : ℤ), Val.int (sp.S : ℤ)] ++ env sp R) (Val.int (sp.y : ℤ)) T U
      (by simp only [List.length_append, List.length_cons, List.length_nil, len_env]; omega)
      (by simp [env_eq_env9, env9])
      (le_trans (step_ht (X := [Val.int (sp.b : ℤ), Val.int (sp.S : ℤ)]) (n := 11) (by simp) (by simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]; omega) hEnvLe hBig1) hBig33)
      (bud_step' (T := T) (S₀ := S₀) (U := U) hUeq hKpick_le (by norm_num))
  have hA1_3 : WordR main chunkP
      (fun vs => vs = [Val.int (sp.y : ℤ), Val.int (sp.b : ℤ), Val.int (sp.S : ℤ)] ++ env sp R)
      (fun _ out => out = [intList (HvdH.chunks sp.y sp.b sp.S)] ++ env sp R) (fun _ => U) := by
    refine chunkEx (chunkP := chunkP) (Kch := Kch) hchunk sp.y sp.b sp.S (env sp R) U hb1 hypowS ?_
    refine bud_big' (T := T) (S₀ := S₀) (U := U) hUeq hKch_le ?_
    have c1 : isz (sp.y : ℤ) ≤ 2 * Big := by
      have c2 : isz (sp.y : ℤ) = sp.y.size + 2 := by simp [HvdH.isz]
      rw [c2, hBig]; omega
    have c2 : sp.S * (sp.b + 1) ≤ Big := by
      have c3 : sp.S * (sp.b + 1) ≤ A2 := by
        rw [hA2]
        calc sp.S * (sp.b + 1) ≤ (sp.S + 1) * (sp.b + 1) := Nat.mul_le_mul_right _ (by omega)
          _ ≤ ((sp.S + 1) * (sp.b + 1)) * ((sp.p + 1) * (HvdH.D + 1)) := by
              calc ((sp.S + 1) * (sp.b + 1)) = ((sp.S + 1) * (sp.b + 1)) * 1 := (Nat.mul_one _).symm
                _ ≤ ((sp.S + 1) * (sp.b + 1)) * ((sp.p + 1) * (HvdH.D + 1)) := by
                    apply Nat.mul_le_mul_left
                    calc (1 : ℕ) = 1 * 1 := by ring
                      _ ≤ (sp.p + 1) * (HvdH.D + 1) := by gcongr <;> omega
          _ = (sp.S + 1) * (sp.p + 1) * (sp.b + 1) * (HvdH.D + 1) := by ring
      omega
    have c3 : isz (sp.b : ℤ) ≤ 2 * Big := by
      have c4 : isz (sp.b : ℤ) = sp.b.size + 2 := by simp [HvdH.isz]
      have c5 : sp.b.size ≤ sp.b := Nat.size_le.mpr (Nat.lt_pow_self (by norm_num : 1 < 2))
      rw [c4, hBig]; omega
    have c4 : isz (sp.S : ℤ) ≤ 2 * Big := by
      have c5 : isz (sp.S : ℤ) = sp.S.size + 2 := by simp [HvdH.isz]
      have c6 : sp.S.size + 2 ≤ 2 * A1 := by
        have c7 : sp.S.size ≤ A1 := by
          rw [hA1]
          calc sp.S.size ≤ (sp.S + 1) * (sp.S.size + 1) := by nlinarith [Nat.zero_le sp.S]
            _ ≤ (sp.S + 1) * (vsz (intList sp.ss) + vsz (intList sp.ts) + sp.b + sp.p + 1) * (sp.S.size + 1) := by
                rw [show (sp.S + 1) * (sp.S.size + 1) = (sp.S + 1) * 1 * (sp.S.size + 1) by ring]
                exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
        have c8 : 2 ≤ A1 := by
          rw [hA1]
          calc (2 : ℕ) = 2 * 1 * 1 := by ring
            _ ≤ (sp.S + 1) * (vsz (intList sp.ss) + vsz (intList sp.ts) + sp.b + sp.p + 1) * (sp.S.size + 1) := by
                gcongr <;> omega
        omega
      rw [c5]; omega
    rw [hT]; omega
  have hA1_4 : WordR main (pickP 4)
      (fun vs => vs = [intList (HvdH.chunks sp.y sp.b sp.S)] ++ env sp R)
      (fun _ out => out = [Val.int (sp.p : ℤ), intList (HvdH.chunks sp.y sp.b sp.S)] ++ env sp R) (fun _ => U) :=
    pickEx hKer hpick 4 ([intList (HvdH.chunks sp.y sp.b sp.S)] ++ env sp R) (Val.int (sp.p : ℤ)) T U
      (by simp only [List.length_append, List.length_cons, List.length_nil, len_env]; omega)
      (by simp [env_eq_env9, env9])
      (le_trans (step_ht (X := [intList (HvdH.chunks sp.y sp.b sp.S)]) (n := 5) (by simp) (by simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]; omega) hEnvLe hBig1) hBig33)
      (bud_step' (T := T) (S₀ := S₀) (U := U) hUeq hKpick_le (by norm_num))
  have hA1_5 : WordR main (pickP 4)
      (fun vs => vs = [Val.int (sp.p : ℤ), intList (HvdH.chunks sp.y sp.b sp.S)] ++ env sp R)
      (fun _ out => out = [Val.int (sp.b : ℤ), Val.int (sp.p : ℤ), intList (HvdH.chunks sp.y sp.b sp.S)] ++ env sp R) (fun _ => U) :=
    pickEx hKer hpick 4 ([Val.int (sp.p : ℤ), intList (HvdH.chunks sp.y sp.b sp.S)] ++ env sp R) (Val.int (sp.b : ℤ)) T U
      (by simp only [List.length_append, List.length_cons, List.length_nil, len_env]; omega)
      (by simp [env_eq_env9, env9])
      (le_trans (step_ht (X := [Val.int (sp.p : ℤ), intList (HvdH.chunks sp.y sp.b sp.S)]) (n := 5) (by simp) (by simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]; omega) hEnvLe hBig1) hBig33)
      (bud_step' (T := T) (S₀ := S₀) (U := U) hUeq hKpick_le (by norm_num))
  have hA1_6 : WordR main (rollP 1)
      (fun vs => vs = [Val.int (sp.b : ℤ), Val.int (sp.p : ℤ), intList (HvdH.chunks sp.y sp.b sp.S)] ++ env sp R)
      (fun _ out => out = [Val.int (sp.p : ℤ), Val.int (sp.b : ℤ), intList (HvdH.chunks sp.y sp.b sp.S)] ++ env sp R) (fun _ => U) :=
    rollEx hKer hroll 1 ([Val.int (sp.b : ℤ), Val.int (sp.p : ℤ), intList (HvdH.chunks sp.y sp.b sp.S)] ++ env sp R)
      ([Val.int (sp.p : ℤ), Val.int (sp.b : ℤ), intList (HvdH.chunks sp.y sp.b sp.S)] ++ env sp R) T U
      (by simp only [List.length_append, List.length_cons, List.length_nil, len_env]; omega)
      (by simp [List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.getD_cons_zero, List.getD_cons_succ])
      (le_trans (step_ht (X := [Val.int (sp.b : ℤ), Val.int (sp.p : ℤ), intList (HvdH.chunks sp.y sp.b sp.S)]) (n := 2) (by simp) (by simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]; omega) hEnvLe hBig1) hBig33)
      (bud_step' (T := T) (S₀ := S₀) (U := U) hUeq hKroll_le (by norm_num))
  have hA1_7 : WordR main (rollP 2)
      (fun vs => vs = [Val.int (sp.p : ℤ), Val.int (sp.b : ℤ), intList (HvdH.chunks sp.y sp.b sp.S)] ++ env sp R)
      (fun _ out => out = [intList (HvdH.chunks sp.y sp.b sp.S), Val.int (sp.p : ℤ), Val.int (sp.b : ℤ)] ++ env sp R) (fun _ => U) :=
    rollEx hKer hroll 2 ([Val.int (sp.p : ℤ), Val.int (sp.b : ℤ), intList (HvdH.chunks sp.y sp.b sp.S)] ++ env sp R)
      ([intList (HvdH.chunks sp.y sp.b sp.S), Val.int (sp.p : ℤ), Val.int (sp.b : ℤ)] ++ env sp R) T U
      (by simp only [List.length_append, List.length_cons, List.length_nil, len_env]; omega)
      (by simp [List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.getD_cons_zero, List.getD_cons_succ])
      (le_trans (step_ht (X := [Val.int (sp.p : ℤ), Val.int (sp.b : ℤ), intList (HvdH.chunks sp.y sp.b sp.S)]) (n := 3) (by simp) (by simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]; omega) hEnvLe hBig1) hBig33)
      (bud_step' (T := T) (S₀ := S₀) (U := U) hUeq hKroll_le (by norm_num))
  have hch1 : WordR main yA8 (fun vs => vs = env sp R)
      (fun _ out => out = [intList (HvdH.chunks sp.y sp.b sp.S), Val.int (sp.p : ℤ), Val.int (sp.b : ℤ)] ++ env sp R)
      (fun _ => U + (U + (U + (U + (U + (U + (U + U))))))) :=
    seqE hKer hA1_0 (seqE hKer hA1_1 (seqE hKer hA1_2 (seqE hKer hA1_3 (seqE hKer hA1_4 (seqE hKer hA1_5 (seqE hKer hA1_6 hA1_7))))))
  have h9y : WordR main toCfxP
      (fun vs => vs = [intList (HvdH.chunks sp.y sp.b sp.S), Val.int (sp.p : ℤ), Val.int (sp.b : ℤ)] ++ env sp R)
      (fun _ out => ∃ (ws1 : List (ℤ × ℤ)),
        (out = [cvecVal ws1, Val.int (sp.p : ℤ), Val.int (sp.b : ℤ)] ++ env sp R) ∧
        (ws1.length = sp.S) ∧
        (∀ j < sp.S, ws1.getD j (0,0) = (scaledChunk (sp.p - sp.b) (HvdH.chunks sp.y sp.b sp.S) j)))
      (fun _ => U)
      := by
    have hcore : WordR main toCfxP
        (fun vs => vs = intList (HvdH.chunks sp.y sp.b sp.S) :: Val.int (sp.p : ℤ) :: Val.int (sp.b : ℤ) :: env sp R)
        (fun _ out => ∃ (ws : List (ℤ × ℤ)),
          (out = cvecVal ws :: Val.int (sp.p : ℤ) :: Val.int (sp.b : ℤ) :: env sp R) ∧
          (ws.length = (HvdH.chunks sp.y sp.b sp.S).length) ∧
          (∀ j < (HvdH.chunks sp.y sp.b sp.S).length,
            ws.getD j (0,0) = (scaledChunk (sp.p - sp.b) (HvdH.chunks sp.y sp.b sp.S) j)))
        (fun _ => U)
        :=
      toCfxEx (toCfxP := toCfxP) (Kto := Kto) hto sp.p sp.b (HvdH.chunks sp.y sp.b sp.S) (env sp R) U hbp
        (fun j hj => chunks_lt sp.y sp.b sp.S j hj) ?_
    · intro vs hvs s R0 hs
      obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ := hcore vs hvs s R0 hs
      obtain ⟨ws1, hout, hwl1, hw1⟩ := hpost
      refine ⟨out, s', n, ⟨ws1, hout, ?_, ?_⟩, hev, hn, hstk, hfr⟩
      · rw [hwl1, Work.IntLib.chunks_length]
      · intro j hj
        rw [hw1 j (by rw [Work.IntLib.chunks_length]; exact hj)]
    · have heq : Kto * ((HvdH.chunks sp.y sp.b sp.S).length + 1) * (sp.p + 1) + Kto
            = Kto * (((HvdH.chunks sp.y sp.b sp.S).length + 1) * (sp.p + 1) + 1) := by ring
      rw [heq]
      refine bud_big' (T := T) (S₀ := S₀) (U := U) hUeq hKto_le ?_
      have h1 : (HvdH.chunks sp.y sp.b sp.S).length = sp.S := Work.IntLib.chunks_length sp.y sp.b sp.S
      rw [h1, hT]
      have h3 : (sp.S + 1) * (sp.p + 1) + 1 ≤ 2 * A2 := by
        have h4 : (sp.S + 1) * (sp.p + 1) ≤ A2 := by
          rw [hA2]
          calc (sp.S + 1) * (sp.p + 1) = ((sp.S + 1) * (sp.p + 1)) * 1 := (Nat.mul_one _).symm
            _ ≤ ((sp.S + 1) * (sp.p + 1)) * ((sp.b + 1) * (HvdH.D + 1)) := by
                apply Nat.mul_le_mul_left
                calc (1 : ℕ) = 1 * 1 := by ring
                  _ ≤ (sp.b + 1) * (HvdH.D + 1) := by gcongr <;> omega
            _ = (sp.S + 1) * (sp.p + 1) * (sp.b + 1) * (HvdH.D + 1) := by ring
        omega
      omega
  have hyC : ∀ (ws1 : List (ℤ × ℤ)), ws1.length = sp.S →
      (∀ j < sp.S, ws1.getD j (0,0) = (scaledChunk (sp.p - sp.b) (HvdH.chunks sp.y sp.b sp.S) j)) →
      WordR main yC
        (fun vs => vs = [cvecVal ws1, Val.int (sp.p : ℤ), Val.int (sp.b : ℤ)] ++ env sp R)
        (fun _ out => ∃ (ys1 : List Val),
          (out = ofList ys1 :: env sp R) ∧
          (ys1.length = sp.ss.prod) ∧
          (∀ m < sp.ss.prod, ys1.getD (HvdH.crtIdx sp.ss m) .nil = (ws1.map cfxVal).getD m .nil))
        (fun _ => U + (U + (U + (U + (U + (U + (U)))))) + U)
        := by
    intro ws1 hwl1 hw1
    have hWsz1 : vsz (cvecVal ws1) ≤ 2 * Big := by
      have h := vsz_ofList_map_le (zs := ws1) (xs := HvdH.chunks sp.y sp.b sp.S) (b := sp.b) (p := sp.p) hbp
        (fun j hj => chunks_lt sp.y sp.b sp.S j hj) (by rw [hwl1, Work.IntLib.chunks_length])
        (fun j hj => hw1 j (by rwa [Work.IntLib.chunks_length] at hj))
      rw [hwl1] at h
      have h2 : sp.S * (2 * sp.p + 6) + 1 ≤ 2 * A2 := hLx2
      have h3 : 2 * A2 ≤ 2 * Big := Nat.mul_le_mul_left _ hA2le
      have h4 := le_trans h (le_trans h2 h3)
      have h5 : vsz (cvecVal ws1) = vsz (ofList (ws1.map cfxVal)) := rfl
      rw [h5]
      exact h4
    have hz1 : WordR main (rollP 1)
        (fun vs => vs = [cvecVal ws1, Val.int (sp.p : ℤ), Val.int (sp.b : ℤ)] ++ env sp R)
        (fun _ out => out = [Val.int (sp.p : ℤ), cvecVal ws1, Val.int (sp.b : ℤ)] ++ env sp R) (fun _ => U) :=
      rollEx hKer hroll 1 ([cvecVal ws1, Val.int (sp.p : ℤ), Val.int (sp.b : ℤ)] ++ env sp R)
        ([Val.int (sp.p : ℤ), cvecVal ws1, Val.int (sp.b : ℤ)] ++ env sp R) T U
        (by simp only [List.length_append, List.length_cons, List.length_nil, len_env]; omega)
        (by simp [List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.getD_cons_zero, List.getD_cons_succ])
        (le_trans (step_ht (X := [cvecVal ws1, Val.int (sp.p : ℤ), Val.int (sp.b : ℤ)]) (n := 2) (by simp)
          (by simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]; omega) hEnvLe hBig1) hBig33)
        (bud_step' (T := T) (S₀ := S₀) (U := U) hUeq hKroll_le (by norm_num))
    have hz2 : WordR main dropP
        (fun vs => vs = [Val.int (sp.p : ℤ), cvecVal ws1, Val.int (sp.b : ℤ)] ++ env sp R)
        (fun _ out => out = [cvecVal ws1, Val.int (sp.b : ℤ)] ++ env sp R) (fun _ => U) :=
      dropEx hKer hdrop (Val.int (sp.p : ℤ)) ([cvecVal ws1, Val.int (sp.b : ℤ)] ++ env sp R) U
        (bud_small' (T := T) (S₀ := S₀) (U := U) hUeq hKdrop_le (by rw [hT]; omega))
    have hz3 : WordR main (rollP 1)
        (fun vs => vs = [cvecVal ws1, Val.int (sp.b : ℤ)] ++ env sp R)
        (fun _ out => out = [Val.int (sp.b : ℤ), cvecVal ws1] ++ env sp R) (fun _ => U) :=
      rollEx hKer hroll 1 ([cvecVal ws1, Val.int (sp.b : ℤ)] ++ env sp R)
        ([Val.int (sp.b : ℤ), cvecVal ws1] ++ env sp R) T U
        (by simp only [List.length_append, List.length_cons, List.length_nil, len_env]; omega)
        (by simp [List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.getD_cons_zero, List.getD_cons_succ])
        (le_trans (step_ht (X := [cvecVal ws1, Val.int (sp.b : ℤ)]) (n := 2) (by simp)
          (by simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]; omega) hEnvLe hBig1) hBig33)
        (bud_step' (T := T) (S₀ := S₀) (U := U) hUeq hKroll_le (by norm_num))
    have hz4 : WordR main dropP
        (fun vs => vs = [Val.int (sp.b : ℤ), cvecVal ws1] ++ env sp R)
        (fun _ out => out = [cvecVal ws1] ++ env sp R) (fun _ => U) :=
      dropEx hKer hdrop (Val.int (sp.b : ℤ)) ([cvecVal ws1] ++ env sp R) U
        (bud_small' (T := T) (S₀ := S₀) (U := U) hUeq hKdrop_le (by rw [hT]; omega))
    have hz5 : WordR main (pushP (Val.int 0))
        (fun vs => vs = [cvecVal ws1] ++ env sp R)
        (fun _ out => out = [Val.int (0 : ℤ), cvecVal ws1] ++ env sp R) (fun _ => U) :=
      pushValEx hKer hpush (Val.int 0) ([cvecVal ws1] ++ env sp R) U
        (bud_small' (T := T) (S₀ := S₀) (U := U) hUeq hKpush_le (by rw [hT]; omega))
    have hz6 : WordR main (pickP 8)
        (fun vs => vs = [Val.int (0 : ℤ), cvecVal ws1] ++ env sp R)
        (fun _ out => out = [intList sp.ss, Val.int (0 : ℤ), cvecVal ws1] ++ env sp R) (fun _ => U) :=
      pickEx hKer hpick 8 ([Val.int (0 : ℤ), cvecVal ws1] ++ env sp R) (intList sp.ss) T U
        (by simp only [List.length_append, List.length_cons, List.length_nil, len_env]; omega)
        (by simp [env_eq_env9, env9])
        (le_trans (step_ht (X := [Val.int (0 : ℤ), cvecVal ws1]) (n := 9) (by simp)
          (by simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]; omega) hEnvLe hBig1) hBig33)
        (bud_step' (T := T) (S₀ := S₀) (U := U) hUeq hKpick_le (by norm_num))
    have hz7 : WordR main swapP
        (fun vs => vs = [intList sp.ss, Val.int (0 : ℤ), cvecVal ws1] ++ env sp R)
        (fun _ out => out = [Val.int (0 : ℤ), intList sp.ss, cvecVal ws1] ++ env sp R) (fun _ => U) :=
      swapEx hKer hswap (intList sp.ss) (Val.int (0 : ℤ)) ([cvecVal ws1] ++ env sp R) T U
        (by rw [hT]; omega)
        (bud_T (T := T) (S₀ := S₀) (U := U) hUeq hKswap_le)
    have hz7c : WordR main yD1
        (fun vs => vs = [cvecVal ws1, Val.int (sp.p : ℤ), Val.int (sp.b : ℤ)] ++ env sp R)
        (fun _ out => out = [Val.int (0 : ℤ), intList sp.ss, cvecVal ws1] ++ env sp R)
        (fun _ => U + (U + (U + (U + (U + (U + U)))))) :=
      seqE hKer hz1 (seqE hKer hz2 (seqE hKer hz3 (seqE hKer hz4 (seqE hKer hz5 (seqE hKer hz6 hz7)))))
    have hz8 : WordR main crtP
        (fun vs => vs = [Val.int (0 : ℤ), intList sp.ss, cvecVal ws1] ++ env sp R)
        (fun _ out => ∃ ys1, out = ofList ys1 :: env sp R ∧ ys1.length = sp.ss.prod ∧
          ∀ m < sp.ss.prod, ys1.getD (HvdH.crtIdx sp.ss m) .nil = (ws1.map cfxVal).getD m .nil)
        (fun _ => U) := by
      refine crtEx (crtP := crtP) (Kcrt := Kcrt) hcrt sp.ss (ws1.map cfxVal) (env sp R) U hs1 hcop ?_ ?_
      · rw [List.length_map, hwl1, hSp]
      · have hWsBound : vsz (ofList (ws1.map cfxVal)) ≤ sp.S * (2 * sp.p + 6) + 1 := by
          have h := vsz_ofList_map_le (zs := ws1) (xs := HvdH.chunks sp.y sp.b sp.S) (b := sp.b) (p := sp.p) hbp
            (fun j hj => chunks_lt sp.y sp.b sp.S j hj) (by rw [hwl1, Work.IntLib.chunks_length])
            (fun j hj => hw1 j (by rwa [Work.IntLib.chunks_length] at hj))
          rw [hwl1] at h
          exact h
        have hinner : (vsz (ofList (ws1.map cfxVal)) + sp.ss.prod * (vsz (intList sp.ss) + 1) + 1)
            * (sp.ss.prod.size + 1) ≤ 1000 * T := by
          rw [← hSp]
          calc (vsz (ofList (ws1.map cfxVal)) + sp.S * (vsz (intList sp.ss) + 1) + 1) * (sp.S.size + 1)
              ≤ 10 * ((sp.S + 1) * (vsz (intList sp.ss) + vsz (intList sp.ts) + sp.b + sp.p + 1) * (sp.S.size + 1)) :=
                crt_inner_le (S := sp.S) (p := sp.p) (b := sp.b) (vszss := vsz (intList sp.ss))
                  (vszts := vsz (intList sp.ts)) (vszW := vsz (ofList (ws1.map cfxVal))) (szS := sp.S.size + 1)
                  hWsBound hb1
            _ = 10 * A1 := by rw [hA1]
            _ ≤ 1000 * T := by rw [hT, hBig]; nlinarith [hBig1]
        have hc : Kcrt * (vsz (ofList (ws1.map cfxVal)) + sp.ss.prod * (vsz (intList sp.ss) + 1) + 1)
              * (sp.ss.prod.size + 1) ≤ U := by
          calc Kcrt * (vsz (ofList (ws1.map cfxVal)) + sp.ss.prod * (vsz (intList sp.ss) + 1) + 1)
              * (sp.ss.prod.size + 1)
              = Kcrt * ((vsz (ofList (ws1.map cfxVal)) + sp.ss.prod * (vsz (intList sp.ss) + 1) + 1)
                  * (sp.ss.prod.size + 1)) := by ring
            _ ≤ S₀ * (1000 * T) := Nat.mul_le_mul hKcrt_le hinner
            _ = U := by rw [hUeq]; ring
        exact hc
    exact seqGen hKer hz7c hz8
  have hyCQ : WordR main yC
      (fun vs => ∃ (ws1 : List (ℤ × ℤ)),
        (vs = [cvecVal ws1, Val.int (sp.p : ℤ), Val.int (sp.b : ℤ)] ++ env sp R) ∧
        (ws1.length = sp.S) ∧
        (∀ j < sp.S, ws1.getD j (0,0) = (scaledChunk (sp.p - sp.b) (HvdH.chunks sp.y sp.b sp.S) j)))
      (fun _ out => ∃ (ws1 : List (ℤ × ℤ)) (ys1 : List Val),
        (out = ofList ys1 :: env sp R) ∧
        (ws1.length = sp.S) ∧
        (∀ j < sp.S, ws1.getD j (0,0) = (scaledChunk (sp.p - sp.b) (HvdH.chunks sp.y sp.b sp.S) j)) ∧
        (ys1.length = sp.ss.prod) ∧
        (∀ m < sp.ss.prod, ys1.getD (HvdH.crtIdx sp.ss m) .nil = (ws1.map cfxVal).getD m .nil))
      (fun _ => U + (U + (U + (U + (U + (U + (U)))))) + U)
      := by
    intro vs hvs s R0 hs
    obtain ⟨ws1, rfl, hwl1, hw1⟩ := hvs
    obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ :=
      hyC ws1 hwl1 hw1 ([cvecVal ws1, Val.int (sp.p : ℤ), Val.int (sp.b : ℤ)] ++ env sp R) rfl s R0 hs
    obtain ⟨ys1, hout, hyl1, hge1⟩ := hpost
    exact ⟨out, s', n, ⟨ws1, ys1, hout, hwl1, hw1, hyl1, hge1⟩, hev, hn, hstk, hfr⟩
  have htok : WordR main (.seq yA8 toCfxP) (fun vs => vs = env sp R)
      (fun _ out => ∃ (ws1 : List (ℤ × ℤ)),
        (out = [cvecVal ws1, Val.int (sp.p : ℤ), Val.int (sp.b : ℤ)] ++ env sp R) ∧
        (ws1.length = sp.S) ∧
        (∀ j < sp.S, ws1.getD j (0,0) = (scaledChunk (sp.p - sp.b) (HvdH.chunks sp.y sp.b sp.S) j)))
      (fun _ => U + (U + (U + (U + (U + (U + (U + (U))))))) + U)
      :=
    seqGen hKer hch1 h9y
  have hyP : WordR main yP (fun vs => vs = env sp R)
      (fun _ out => ∃ (ws1 : List (ℤ × ℤ)) (ys1 : List Val),
        (out = ofList ys1 :: env sp R) ∧
        (ws1.length = sp.S) ∧
        (∀ j < sp.S, ws1.getD j (0,0) = (scaledChunk (sp.p - sp.b) (HvdH.chunks sp.y sp.b sp.S) j)) ∧
        (ys1.length = sp.ss.prod) ∧
        (∀ m < sp.ss.prod, ys1.getD (HvdH.crtIdx sp.ss m) .nil = (ws1.map cfxVal).getD m .nil))
        (fun _ => (U + (U + (U + (U + (U + (U + (U + (U))))))) + U) + (U + (U + (U + (U + (U + (U + (U)))))) + U))
        :=
    seqGen hKer htok hyCQ
  have hy1 : WordR main yP (fun vs => vs = env sp R)
      (fun _ out => ∃ (G : List (ℤ × ℤ)),
        (out = cvecVal G :: env sp R) ∧
        (G.length = sp.S) ∧
        (∀ m < sp.S, G.getD (HvdH.crtIdx sp.ss m) (0,0) = pchunkZ sp.y sp.b sp.N' sp.S (sp.p - sp.b) m) ∧
        (vsz (cvecVal G) ≤ 2 * Big))
        (fun _ => (U + (U + (U + (U + (U + (U + (U + (U))))))) + U) + (U + (U + (U + (U + (U + (U + (U)))))) + U))
        := by
    intro vs hvs s R0 hs
    obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ := hyP vs hvs s R0 hs
    obtain ⟨ws1, ys1, hout, hwl1, hw1, hyl1, hge1⟩ := hpost
    obtain ⟨G, hys1, hGl, hGg⟩ := crtExtract hs1 hcop (by rw [hwl1, hSp]) (by rw [hyl1]) hge1
    have hGsz : vsz (cvecVal G) ≤ 2 * Big := by
      have hFl : G.length = sp.S := by rw [hGl, hSp]
      have hFp : ∀ m < sp.S, G.getD (HvdH.crtIdx sp.ss m) (0,0) = pchunkZ sp.y sp.b sp.N' sp.S (sp.p - sp.b) m := by
        intro m hm
        rw [hGg m (by rw [← hSp]; exact hm), hw1 m hm, scaledChunk_getD_pchunk hNS hypowN hm] <;> simp only [pchunkZ, pchunkN]
      have h1 := cvecValSizePrep (S := sp.S) (N' := sp.N') (b := sp.b) (p := sp.p) (ss := sp.ss) (x := sp.y) (F := G)
        hs1 hcop hSp hbp hFl hFp
      exact le_trans h1 (le_trans hLx2 (Nat.mul_le_mul_left _ hA2le))
    refine ⟨out, s', n, ⟨G, ?_, ?_, ?_, hGsz⟩, hev, hn, hstk, hfr⟩
    · rw [hout, hys1] <;> simp only [cvecVal]
    · rw [hGl, hSp]
    · intro m hm
      rw [hGg m (by rw [← hSp]; exact hm), hw1 m hm, scaledChunk_getD_pchunk hNS hypowN hm] <;> simp only [pchunkZ, pchunkN]
  -- ################ STAGE 2 (argument x) ################
  have hxP : WordR main xP
      (fun vs => ∃ G, vs = cvecVal G :: env sp R ∧ G.length = sp.S ∧
        (∀ m < sp.S, G.getD (HvdH.crtIdx sp.ss m) (0,0) = pchunkZ sp.y sp.b sp.N' sp.S (sp.p - sp.b) m) ∧
        vsz (cvecVal G) ≤ 2 * Big)
      (fun _ out => ∃ G F, out = cvecVal F :: cvecVal G :: env sp R ∧ G.length = sp.S ∧
        (∀ m < sp.S, G.getD (HvdH.crtIdx sp.ss m) (0,0) = pchunkZ sp.y sp.b sp.N' sp.S (sp.p - sp.b) m) ∧
        vsz (cvecVal G) ≤ 2 * Big ∧ F.length = sp.S ∧
        (∀ m < sp.S, F.getD (HvdH.crtIdx sp.ss m) (0,0) = pchunkZ sp.x sp.b sp.N' sp.S (sp.p - sp.b) m))
      (fun _ => (U + (U + (U + (U + (U + (U + (U + (U))))))) + U) + (U + (U + (U + (U + (U + (U + (U)))))) + U)) := by
    intro vs hvs s R0 hs
    obtain ⟨G, rfl, hGl, hGg, hGsz⟩ := hvs
    have hB2_0 : WordR main (pickP 1)
        (fun vs => vs = cvecVal G :: env sp R)
        (fun _ out => out = [Val.int (sp.S : ℤ), cvecVal G] ++ env sp R) (fun _ => U) :=
      pickEx hKer hpick 1 ([cvecVal G] ++ env sp R) (Val.int (sp.S : ℤ)) T U
        (by simp only [List.length_append, List.length_cons, List.length_nil, len_env]; omega)
        (by simp [env_eq_env9, env9])
        (le_trans (step_ht (X := [cvecVal G]) (n := 2) (by simp) (by simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]; omega) hEnvLe hBig1) hBig33)
        (bud_step' (T := T) (S₀ := S₀) (U := U) hUeq hKpick_le (by norm_num))
    have hB2_1 : WordR main (pickP 4)
        (fun vs => vs = [Val.int (sp.S : ℤ), cvecVal G] ++ env sp R)
        (fun _ out => out = [Val.int (sp.b : ℤ), Val.int (sp.S : ℤ), cvecVal G] ++ env sp R) (fun _ => U) :=
      pickEx hKer hpick 4 ([Val.int (sp.S : ℤ), cvecVal G] ++ env sp R) (Val.int (sp.b : ℤ)) T U
        (by simp only [List.length_append, List.length_cons, List.length_nil, len_env]; omega)
        (by simp [env_eq_env9, env9])
        (le_trans (step_ht (X := [Val.int (sp.S : ℤ), cvecVal G]) (n := 5) (by simp) (by simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]; omega) hEnvLe hBig1) hBig33)
        (bud_step' (T := T) (S₀ := S₀) (U := U) hUeq hKpick_le (by norm_num))
    have hB2_2 : WordR main (pickP 10)
        (fun vs => vs = [Val.int (sp.b : ℤ), Val.int (sp.S : ℤ), cvecVal G] ++ env sp R)
        (fun _ out => out = [Val.int (sp.x : ℤ), Val.int (sp.b : ℤ), Val.int (sp.S : ℤ), cvecVal G] ++ env sp R) (fun _ => U) :=
      pickEx hKer hpick 10 ([Val.int (sp.b : ℤ), Val.int (sp.S : ℤ), cvecVal G] ++ env sp R) (Val.int (sp.x : ℤ)) T U
        (by simp only [List.length_append, List.length_cons, List.length_nil, len_env]; omega)
        (by simp [env_eq_env9, env9])
        (le_trans (step_ht (X := [Val.int (sp.b : ℤ), Val.int (sp.S : ℤ), cvecVal G]) (n := 11) (by simp) (by simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]; omega) hEnvLe hBig1) hBig33)
        (bud_step' (T := T) (S₀ := S₀) (U := U) hUeq hKpick_le (by norm_num))
    have hB2_3 : WordR main chunkP
        (fun vs => vs = [Val.int (sp.x : ℤ), Val.int (sp.b : ℤ), Val.int (sp.S : ℤ), cvecVal G] ++ env sp R)
        (fun _ out => out = [intList (HvdH.chunks sp.x sp.b sp.S), cvecVal G] ++ env sp R) (fun _ => U) := by
      refine chunkEx (chunkP := chunkP) (Kch := Kch) hchunk sp.x sp.b sp.S (cvecVal G :: env sp R) U hb1 hxpowS ?_
      refine bud_big' (T := T) (S₀ := S₀) (U := U) hUeq hKch_le ?_
      have c1 : isz (sp.x : ℤ) ≤ 2 * Big := by
        have c2 : isz (sp.x : ℤ) = sp.x.size + 2 := by simp [HvdH.isz]
        rw [c2, hBig]; omega
      have c2 : sp.S * (sp.b + 1) ≤ Big := by
        have c3 : sp.S * (sp.b + 1) ≤ A2 := by
          rw [hA2]
          calc sp.S * (sp.b + 1) ≤ (sp.S + 1) * (sp.b + 1) := Nat.mul_le_mul_right _ (by omega)
            _ ≤ ((sp.S + 1) * (sp.b + 1)) * ((sp.p + 1) * (HvdH.D + 1)) := by
                calc ((sp.S + 1) * (sp.b + 1)) = ((sp.S + 1) * (sp.b + 1)) * 1 := (Nat.mul_one _).symm
                  _ ≤ ((sp.S + 1) * (sp.b + 1)) * ((sp.p + 1) * (HvdH.D + 1)) := by
                      apply Nat.mul_le_mul_left
                      calc (1 : ℕ) = 1 * 1 := by ring
                        _ ≤ (sp.p + 1) * (HvdH.D + 1) := by gcongr <;> omega
            _ = (sp.S + 1) * (sp.p + 1) * (sp.b + 1) * (HvdH.D + 1) := by ring
        omega
      have c3 : isz (sp.b : ℤ) ≤ 2 * Big := by
        have c4 : isz (sp.b : ℤ) = sp.b.size + 2 := by simp [HvdH.isz]
        have c5 : sp.b.size ≤ sp.b := Nat.size_le.mpr (Nat.lt_pow_self (by norm_num : 1 < 2))
        rw [c4, hBig]; omega
      have c4 : isz (sp.S : ℤ) ≤ 2 * Big := by
        have c5 : isz (sp.S : ℤ) = sp.S.size + 2 := by simp [HvdH.isz]
        have c6 : sp.S.size + 2 ≤ 2 * A1 := by
          have c7 : sp.S.size ≤ A1 := by
            rw [hA1]
            calc sp.S.size ≤ (sp.S + 1) * (sp.S.size + 1) := by nlinarith [Nat.zero_le sp.S]
              _ ≤ (sp.S + 1) * (vsz (intList sp.ss) + vsz (intList sp.ts) + sp.b + sp.p + 1) * (sp.S.size + 1) := by
                  rw [show (sp.S + 1) * (sp.S.size + 1) = (sp.S + 1) * 1 * (sp.S.size + 1) by ring]
                  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
          have c8 : 2 ≤ A1 := by
            rw [hA1]
            calc (2 : ℕ) = 2 * 1 * 1 := by ring
              _ ≤ (sp.S + 1) * (vsz (intList sp.ss) + vsz (intList sp.ts) + sp.b + sp.p + 1) * (sp.S.size + 1) := by
                  gcongr <;> omega
          omega
        rw [c5]; omega
      rw [hT]; omega
    have hB2_4 : WordR main (pickP 5)
        (fun vs => vs = [intList (HvdH.chunks sp.x sp.b sp.S), cvecVal G] ++ env sp R)
        (fun _ out => out = [Val.int (sp.p : ℤ), intList (HvdH.chunks sp.x sp.b sp.S), cvecVal G] ++ env sp R) (fun _ => U) :=
      pickEx hKer hpick 5 ([intList (HvdH.chunks sp.x sp.b sp.S), cvecVal G] ++ env sp R) (Val.int (sp.p : ℤ)) T U
        (by simp only [List.length_append, List.length_cons, List.length_nil, len_env]; omega)
        (by simp [env_eq_env9, env9])
        (le_trans (step_ht (X := [intList (HvdH.chunks sp.x sp.b sp.S), cvecVal G]) (n := 6) (by simp) (by simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]; omega) hEnvLe hBig1) hBig33)
        (bud_step' (T := T) (S₀ := S₀) (U := U) hUeq hKpick_le (by norm_num))
    have hB2_5 : WordR main (pickP 5)
        (fun vs => vs = [Val.int (sp.p : ℤ), intList (HvdH.chunks sp.x sp.b sp.S), cvecVal G] ++ env sp R)
        (fun _ out => out = [Val.int (sp.b : ℤ), Val.int (sp.p : ℤ), intList (HvdH.chunks sp.x sp.b sp.S), cvecVal G] ++ env sp R) (fun _ => U) :=
      pickEx hKer hpick 5 ([Val.int (sp.p : ℤ), intList (HvdH.chunks sp.x sp.b sp.S), cvecVal G] ++ env sp R) (Val.int (sp.b : ℤ)) T U
        (by simp only [List.length_append, List.length_cons, List.length_nil, len_env]; omega)
        (by simp [env_eq_env9, env9])
        (le_trans (step_ht (X := [Val.int (sp.p : ℤ), intList (HvdH.chunks sp.x sp.b sp.S), cvecVal G]) (n := 6) (by simp) (by simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]; omega) hEnvLe hBig1) hBig33)
        (bud_step' (T := T) (S₀ := S₀) (U := U) hUeq hKpick_le (by norm_num))
    have hB2_6 : WordR main (rollP 1)
        (fun vs => vs = [Val.int (sp.b : ℤ), Val.int (sp.p : ℤ), intList (HvdH.chunks sp.x sp.b sp.S), cvecVal G] ++ env sp R)
        (fun _ out => out = [Val.int (sp.p : ℤ), Val.int (sp.b : ℤ), intList (HvdH.chunks sp.x sp.b sp.S), cvecVal G] ++ env sp R) (fun _ => U) :=
      rollEx hKer hroll 1 ([Val.int (sp.b : ℤ), Val.int (sp.p : ℤ), intList (HvdH.chunks sp.x sp.b sp.S), cvecVal G] ++ env sp R)
        ([Val.int (sp.p : ℤ), Val.int (sp.b : ℤ), intList (HvdH.chunks sp.x sp.b sp.S), cvecVal G] ++ env sp R) T U
        (by simp only [List.length_append, List.length_cons, List.length_nil, len_env]; omega)
        (by simp [List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.getD_cons_zero, List.getD_cons_succ])
        (le_trans (step_ht (X := [Val.int (sp.b : ℤ), Val.int (sp.p : ℤ), intList (HvdH.chunks sp.x sp.b sp.S), cvecVal G]) (n := 2) (by simp) (by simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]; omega) hEnvLe hBig1) hBig33)
        (bud_step' (T := T) (S₀ := S₀) (U := U) hUeq hKroll_le (by norm_num))
    have hB2_7 : WordR main (rollP 2)
        (fun vs => vs = [Val.int (sp.p : ℤ), Val.int (sp.b : ℤ), intList (HvdH.chunks sp.x sp.b sp.S), cvecVal G] ++ env sp R)
        (fun _ out => out = [intList (HvdH.chunks sp.x sp.b sp.S), Val.int (sp.p : ℤ), Val.int (sp.b : ℤ), cvecVal G] ++ env sp R) (fun _ => U) :=
      rollEx hKer hroll 2 ([Val.int (sp.p : ℤ), Val.int (sp.b : ℤ), intList (HvdH.chunks sp.x sp.b sp.S), cvecVal G] ++ env sp R)
        ([intList (HvdH.chunks sp.x sp.b sp.S), Val.int (sp.p : ℤ), Val.int (sp.b : ℤ), cvecVal G] ++ env sp R) T U
        (by simp only [List.length_append, List.length_cons, List.length_nil, len_env]; omega)
        (by simp [List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.getD_cons_zero, List.getD_cons_succ])
        (le_trans (step_ht (X := [Val.int (sp.p : ℤ), Val.int (sp.b : ℤ), intList (HvdH.chunks sp.x sp.b sp.S), cvecVal G]) (n := 3) (by simp) (by simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]; omega) hEnvLe hBig1) hBig33)
        (bud_step' (T := T) (S₀ := S₀) (U := U) hUeq hKroll_le (by norm_num))
    have hxA : WordR main xA8 (fun vs => vs = cvecVal G :: env sp R)
        (fun _ out => out = [intList (HvdH.chunks sp.x sp.b sp.S), Val.int (sp.p : ℤ), Val.int (sp.b : ℤ), cvecVal G] ++ env sp R)
        (fun _ => U + (U + (U + (U + (U + (U + (U + U))))))) :=
      seqE hKer hB2_0 (seqE hKer hB2_1 (seqE hKer hB2_2 (seqE hKer hB2_3 (seqE hKer hB2_4 (seqE hKer hB2_5 (seqE hKer hB2_6 hB2_7))))))
    have h9x : WordR main toCfxP
        (fun vs => vs = [intList (HvdH.chunks sp.x sp.b sp.S), Val.int (sp.p : ℤ), Val.int (sp.b : ℤ), cvecVal G] ++ env sp R)
        (fun _ out => ∃ (ws2 : List (ℤ × ℤ)),
          (out = [cvecVal ws2, Val.int (sp.p : ℤ), Val.int (sp.b : ℤ), cvecVal G] ++ env sp R) ∧
          (ws2.length = sp.S) ∧
          (∀ j < sp.S, ws2.getD j (0,0) = (scaledChunk (sp.p - sp.b) (HvdH.chunks sp.x sp.b sp.S) j)))
        (fun _ => U)
        := by
      have hc : Kto * ((HvdH.chunks sp.x sp.b sp.S).length + 1) * (sp.p + 1) + Kto ≤ U := by
        have heq : Kto * ((HvdH.chunks sp.x sp.b sp.S).length + 1) * (sp.p + 1) + Kto
            = Kto * (((HvdH.chunks sp.x sp.b sp.S).length + 1) * (sp.p + 1) + 1) := by ring
        rw [heq]
        refine bud_big' (T := T) (S₀ := S₀) (U := U) hUeq hKto_le ?_
        rw [Work.IntLib.chunks_length, hT]
        have h3 : (sp.S + 1) * (sp.p + 1) + 1 ≤ 2 * A2 := by
          have h4 : (sp.S + 1) * (sp.p + 1) ≤ A2 := by
            rw [hA2]
            calc (sp.S + 1) * (sp.p + 1) = ((sp.S + 1) * (sp.p + 1)) * 1 := (Nat.mul_one _).symm
              _ ≤ ((sp.S + 1) * (sp.p + 1)) * ((sp.b + 1) * (HvdH.D + 1)) := by
                  apply Nat.mul_le_mul_left
                  calc (1 : ℕ) = 1 * 1 := by ring
                    _ ≤ (sp.b + 1) * (HvdH.D + 1) := by gcongr <;> omega
              _ = (sp.S + 1) * (sp.p + 1) * (sp.b + 1) * (HvdH.D + 1) := by ring
          omega
        first | nlinarith [h3, hA2le, hBig1] | omega
      have hcore : WordR main toCfxP
          (fun vs => vs = intList (HvdH.chunks sp.x sp.b sp.S) :: Val.int (sp.p : ℤ) :: Val.int (sp.b : ℤ) :: cvecVal G :: env sp R)
          (fun _ out => ∃ (ws : List (ℤ × ℤ)),
            (out = cvecVal ws :: Val.int (sp.p : ℤ) :: Val.int (sp.b : ℤ) :: cvecVal G :: env sp R) ∧
            (ws.length = (HvdH.chunks sp.x sp.b sp.S).length) ∧
              (∀ j < (HvdH.chunks sp.x sp.b sp.S).length,
              ws.getD j (0,0) = (scaledChunk (sp.p - sp.b) (HvdH.chunks sp.x sp.b sp.S) j)))
          (fun _ => U)
          :=
        toCfxEx (toCfxP := toCfxP) (Kto := Kto) hto sp.p sp.b (HvdH.chunks sp.x sp.b sp.S) (cvecVal G :: env sp R) U hbp
          (fun j hj => chunks_lt sp.x sp.b sp.S j hj) hc
      intro vs hvs s R0 hs
      obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ := hcore vs hvs s R0 hs
      obtain ⟨ws2, hout, hwl2, hw2⟩ := hpost
      refine ⟨out, s', n, ⟨ws2, hout, ?_, ?_⟩, hev, hn, hstk, hfr⟩
      · rw [hwl2, Work.IntLib.chunks_length]
      · intro j hj
        rw [hw2 j (by rw [Work.IntLib.chunks_length]; exact hj)]
    have hxC : ∀ (ws2 : List (ℤ × ℤ)), ws2.length = sp.S →
        (∀ j < sp.S, ws2.getD j (0,0) = (scaledChunk (sp.p - sp.b) (HvdH.chunks sp.x sp.b sp.S) j)) →
        WordR main xC
          (fun vs => vs = [cvecVal ws2, Val.int (sp.p : ℤ), Val.int (sp.b : ℤ)] ++ cvecVal G :: env sp R)
          (fun _ out => ∃ (ys2 : List Val),
            (out = ofList ys2 :: cvecVal G :: env sp R) ∧
            (ys2.length = sp.ss.prod) ∧
            (∀ m < sp.ss.prod, ys2.getD (HvdH.crtIdx sp.ss m) .nil = (ws2.map cfxVal).getD m .nil))
          (fun _ => U + (U + (U + (U + (U + (U + (U)))))) + U)
          := by
      intro ws2 hwl2 hw2
      have hWsz2 : vsz (cvecVal ws2) ≤ 2 * Big := by
        have h := vsz_ofList_map_le (zs := ws2) (xs := HvdH.chunks sp.x sp.b sp.S) (b := sp.b) (p := sp.p) hbp
          (fun j hj => chunks_lt sp.x sp.b sp.S j hj) (by rw [hwl2, Work.IntLib.chunks_length])
          (fun j hj => hw2 j (by rwa [Work.IntLib.chunks_length] at hj))
        rw [hwl2] at h
        have h2 : sp.S * (2 * sp.p + 6) + 1 ≤ 2 * A2 := hLx2
        have h3 : 2 * A2 ≤ 2 * Big := Nat.mul_le_mul_left _ hA2le
        have h4 := le_trans h (le_trans h2 h3)
        have h5 : vsz (cvecVal ws2) = vsz (ofList (ws2.map cfxVal)) := rfl
        rw [h5]
        exact h4
      have hw1 : WordR main (rollP 1)
          (fun vs => vs = [cvecVal ws2, Val.int (sp.p : ℤ), Val.int (sp.b : ℤ)] ++ cvecVal G :: env sp R)
          (fun _ out => out = [Val.int (sp.p : ℤ), cvecVal ws2, Val.int (sp.b : ℤ)] ++ cvecVal G :: env sp R) (fun _ => U) :=
        rollEx hKer hroll 1 ([cvecVal ws2, Val.int (sp.p : ℤ), Val.int (sp.b : ℤ)] ++ cvecVal G :: env sp R)
          ([Val.int (sp.p : ℤ), cvecVal ws2, Val.int (sp.b : ℤ)] ++ cvecVal G :: env sp R) T U
          (by simp only [List.length_append, List.length_cons, List.length_nil, len_env]; omega)
          (by simp [List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.getD_cons_zero, List.getD_cons_succ])
          (le_trans (step_ht (X := [cvecVal ws2, Val.int (sp.p : ℤ), Val.int (sp.b : ℤ), cvecVal G]) (n := 2) (by simp)
            (by simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]; omega) hEnvLe hBig1) hBig33)
          (bud_step' (T := T) (S₀ := S₀) (U := U) hUeq hKroll_le (by norm_num))
      have hw2' : WordR main dropP
          (fun vs => vs = [Val.int (sp.p : ℤ), cvecVal ws2, Val.int (sp.b : ℤ)] ++ cvecVal G :: env sp R)
          (fun _ out => out = [cvecVal ws2, Val.int (sp.b : ℤ)] ++ cvecVal G :: env sp R) (fun _ => U) :=
        dropEx hKer hdrop (Val.int (sp.p : ℤ)) ([cvecVal ws2, Val.int (sp.b : ℤ)] ++ cvecVal G :: env sp R) U
          (bud_small' (T := T) (S₀ := S₀) (U := U) hUeq hKdrop_le (by rw [hT]; omega))
      have hw3 : WordR main (rollP 1)
          (fun vs => vs = [cvecVal ws2, Val.int (sp.b : ℤ)] ++ cvecVal G :: env sp R)
          (fun _ out => out = [Val.int (sp.b : ℤ), cvecVal ws2] ++ cvecVal G :: env sp R) (fun _ => U) :=
        rollEx hKer hroll 1 ([cvecVal ws2, Val.int (sp.b : ℤ)] ++ cvecVal G :: env sp R)
          ([Val.int (sp.b : ℤ), cvecVal ws2] ++ cvecVal G :: env sp R) T U
          (by simp only [List.length_append, List.length_cons, List.length_nil, len_env]; omega)
          (by simp [List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.getD_cons_zero, List.getD_cons_succ])
          (le_trans (step_ht (X := [cvecVal ws2, Val.int (sp.b : ℤ), cvecVal G]) (n := 2) (by simp)
            (by simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]; omega) hEnvLe hBig1) hBig33)
          (bud_step' (T := T) (S₀ := S₀) (U := U) hUeq hKroll_le (by norm_num))
      have hw4 : WordR main dropP
          (fun vs => vs = [Val.int (sp.b : ℤ), cvecVal ws2] ++ cvecVal G :: env sp R)
          (fun _ out => out = [cvecVal ws2] ++ cvecVal G :: env sp R) (fun _ => U) :=
        dropEx hKer hdrop (Val.int (sp.b : ℤ)) ([cvecVal ws2] ++ cvecVal G :: env sp R) U
          (bud_small' (T := T) (S₀ := S₀) (U := U) hUeq hKdrop_le (by rw [hT]; omega))
      have hw5 : WordR main (pushP (Val.int 0))
          (fun vs => vs = [cvecVal ws2] ++ cvecVal G :: env sp R)
          (fun _ out => out = [Val.int (0 : ℤ), cvecVal ws2] ++ cvecVal G :: env sp R) (fun _ => U) :=
        pushValEx hKer hpush (Val.int 0) ([cvecVal ws2] ++ cvecVal G :: env sp R) U
          (bud_small' (T := T) (S₀ := S₀) (U := U) hUeq hKpush_le (by rw [hT]; omega))
      have hw6 : WordR main (pickP 9)
          (fun vs => vs = [Val.int (0 : ℤ), cvecVal ws2] ++ cvecVal G :: env sp R)
          (fun _ out => out = [intList sp.ss, Val.int (0 : ℤ), cvecVal ws2] ++ cvecVal G :: env sp R) (fun _ => U) :=
        pickEx hKer hpick 9 ([Val.int (0 : ℤ), cvecVal ws2] ++ cvecVal G :: env sp R) (intList sp.ss) T U
          (by simp only [List.length_append, List.length_cons, List.length_nil, len_env]; omega)
          (by simp [env_eq_env9, env9])
          (le_trans (step_ht (X := [Val.int (0 : ℤ), cvecVal ws2, cvecVal G]) (n := 10) (by simp)
            (by simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]; omega) hEnvLe hBig1) hBig33)
          (bud_step' (T := T) (S₀ := S₀) (U := U) hUeq hKpick_le (by norm_num))
      have hw7 : WordR main swapP
          (fun vs => vs = [intList sp.ss, Val.int (0 : ℤ), cvecVal ws2] ++ cvecVal G :: env sp R)
          (fun _ out => out = [Val.int (0 : ℤ), intList sp.ss, cvecVal ws2] ++ cvecVal G :: env sp R) (fun _ => U) :=
        swapEx hKer hswap (intList sp.ss) (Val.int (0 : ℤ)) ([cvecVal ws2] ++ cvecVal G :: env sp R) T U
          (by rw [hT]; omega)
          (bud_T (T := T) (S₀ := S₀) (U := U) hUeq hKswap_le)
      have hw7c : WordR main xD1
          (fun vs => vs = [cvecVal ws2, Val.int (sp.p : ℤ), Val.int (sp.b : ℤ)] ++ cvecVal G :: env sp R)
          (fun _ out => out = [Val.int (0 : ℤ), intList sp.ss, cvecVal ws2] ++ cvecVal G :: env sp R)
          (fun _ => U + (U + (U + (U + (U + (U + U)))))) :=
        seqE hKer hw1 (seqE hKer hw2' (seqE hKer hw3 (seqE hKer hw4 (seqE hKer hw5 (seqE hKer hw6 hw7)))))
      have hw8 : WordR main crtP
          (fun vs => vs = [Val.int (0 : ℤ), intList sp.ss, cvecVal ws2] ++ cvecVal G :: env sp R)
          (fun _ out => ∃ ys2, out = ofList ys2 :: cvecVal G :: env sp R ∧ ys2.length = sp.ss.prod ∧
            ∀ m < sp.ss.prod, ys2.getD (HvdH.crtIdx sp.ss m) .nil = (ws2.map cfxVal).getD m .nil)
          (fun _ => U) := by
        refine crtEx (crtP := crtP) (Kcrt := Kcrt) hcrt sp.ss (ws2.map cfxVal) (cvecVal G :: env sp R) U hs1 hcop ?_ ?_
        · rw [List.length_map, hwl2, hSp]
        · have hWsBound : vsz (ofList (ws2.map cfxVal)) ≤ sp.S * (2 * sp.p + 6) + 1 := by
            have h := vsz_ofList_map_le (zs := ws2) (xs := HvdH.chunks sp.x sp.b sp.S) (b := sp.b) (p := sp.p) hbp
              (fun j hj => chunks_lt sp.x sp.b sp.S j hj) (by rw [hwl2, Work.IntLib.chunks_length])
              (fun j hj => hw2 j (by rwa [Work.IntLib.chunks_length] at hj))
            rw [hwl2] at h
            exact h
          have hinner : (vsz (ofList (ws2.map cfxVal)) + sp.ss.prod * (vsz (intList sp.ss) + 1) + 1)
              * (sp.ss.prod.size + 1) ≤ 1000 * T := by
            rw [← hSp]
            calc (vsz (ofList (ws2.map cfxVal)) + sp.S * (vsz (intList sp.ss) + 1) + 1) * (sp.S.size + 1)
                ≤ 10 * ((sp.S + 1) * (vsz (intList sp.ss) + vsz (intList sp.ts) + sp.b + sp.p + 1) * (sp.S.size + 1)) :=
                  crt_inner_le (S := sp.S) (p := sp.p) (b := sp.b) (vszss := vsz (intList sp.ss))
                    (vszts := vsz (intList sp.ts)) (vszW := vsz (ofList (ws2.map cfxVal))) (szS := sp.S.size + 1)
                    hWsBound hb1
              _ = 10 * A1 := by rw [hA1]
              _ ≤ 1000 * T := by rw [hT, hBig]; nlinarith [hBig1]
          have hc : Kcrt * (vsz (ofList (ws2.map cfxVal)) + sp.ss.prod * (vsz (intList sp.ss) + 1) + 1)
                * (sp.ss.prod.size + 1) ≤ U := by
            calc Kcrt * (vsz (ofList (ws2.map cfxVal)) + sp.ss.prod * (vsz (intList sp.ss) + 1) + 1)
                * (sp.ss.prod.size + 1)
                = Kcrt * ((vsz (ofList (ws2.map cfxVal)) + sp.ss.prod * (vsz (intList sp.ss) + 1) + 1)
                    * (sp.ss.prod.size + 1)) := by ring
              _ ≤ S₀ * (1000 * T) := Nat.mul_le_mul hKcrt_le hinner
              _ = U := by rw [hUeq]; ring
          exact hc
      exact seqGen hKer hw7c hw8
    have hxCQ : WordR main xC
        (fun vs => ∃ (ws2 : List (ℤ × ℤ)),
          (vs = [cvecVal ws2, Val.int (sp.p : ℤ), Val.int (sp.b : ℤ)] ++ cvecVal G :: env sp R) ∧
          (ws2.length = sp.S) ∧
          (∀ j < sp.S, ws2.getD j (0,0) = (scaledChunk (sp.p - sp.b) (HvdH.chunks sp.x sp.b sp.S) j)))
        (fun _ out => ∃ (ws2 : List (ℤ × ℤ)) (ys2 : List Val),
          (out = ofList ys2 :: cvecVal G :: env sp R) ∧
          (ws2.length = sp.S) ∧
          (∀ j < sp.S, ws2.getD j (0,0) = (scaledChunk (sp.p - sp.b) (HvdH.chunks sp.x sp.b sp.S) j)) ∧
          (ys2.length = sp.ss.prod) ∧
          (∀ m < sp.ss.prod, ys2.getD (HvdH.crtIdx sp.ss m) .nil = (ws2.map cfxVal).getD m .nil))
        (fun _ => U + (U + (U + (U + (U + (U + (U)))))) + U)
        := by
      intro vs hvs s R1 hs1'
      obtain ⟨ws2, rfl, hwl2, hw2⟩ := hvs
      obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ :=
        hxC ws2 hwl2 hw2 ([cvecVal ws2, Val.int (sp.p : ℤ), Val.int (sp.b : ℤ)] ++ cvecVal G :: env sp R) rfl s R1 hs1'
      obtain ⟨ys2, hout, hyl2, hge2⟩ := hpost
      exact ⟨out, s', n, ⟨ws2, ys2, hout, hwl2, hw2, hyl2, hge2⟩, hev, hn, hstk, hfr⟩
    have htokx : WordR main (.seq xA8 toCfxP) (fun vs => vs = cvecVal G :: env sp R)
        (fun _ out => ∃ (ws2 : List (ℤ × ℤ)),
          (out = [cvecVal ws2, Val.int (sp.p : ℤ), Val.int (sp.b : ℤ), cvecVal G] ++ env sp R) ∧
          (ws2.length = sp.S) ∧
          (∀ j < sp.S, ws2.getD j (0,0) = (scaledChunk (sp.p - sp.b) (HvdH.chunks sp.x sp.b sp.S) j)))
        (fun _ => U + (U + (U + (U + (U + (U + (U + (U))))))) + U)
        :=
      seqGen hKer hxA h9x
    have hxP0 : WordR main xP (fun vs => vs = cvecVal G :: env sp R)
        (fun _ out => ∃ (ws2 : List (ℤ × ℤ)) (ys2 : List Val),
          (out = ofList ys2 :: cvecVal G :: env sp R) ∧
          (ws2.length = sp.S) ∧
          (∀ j < sp.S, ws2.getD j (0,0) = (scaledChunk (sp.p - sp.b) (HvdH.chunks sp.x sp.b sp.S) j)) ∧
          (ys2.length = sp.ss.prod) ∧
          (∀ m < sp.ss.prod, ys2.getD (HvdH.crtIdx sp.ss m) .nil = (ws2.map cfxVal).getD m .nil))
          (fun _ => (U + (U + (U + (U + (U + (U + (U + (U))))))) + U) + (U + (U + (U + (U + (U + (U + (U)))))) + U))
          :=
      seqGen hKer htokx hxCQ
    obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ := hxP0 (cvecVal G :: env sp R) rfl s R0 hs
    obtain ⟨ws2, ys2, hout, hwl2, hw2, hyl2, hge2⟩ := hpost
    obtain ⟨F, hys2, hFl, hFg⟩ := crtExtract hs1 hcop (by rw [hwl2, hSp]) (by rw [hyl2]) hge2
    have hout2 : out = cvecVal F :: cvecVal G :: env sp R := by rw [hout, hys2] <;> simp only [cvecVal]
    have hFl2 : F.length = sp.S := by rw [hFl, hSp]
    have hFg2 : ∀ m < sp.S, F.getD (HvdH.crtIdx sp.ss m) (0,0) = pchunkZ sp.x sp.b sp.N' sp.S (sp.p - sp.b) m := by
      intro m hm
      rw [hFg m (by rw [← hSp]; exact hm), hw2 m hm,
        scaledChunk_getD_pchunk hNS hxpowN hm] <;> simp only [pchunkZ, pchunkN]
    exact ⟨out, s', n, ⟨G, F, hout2, hGl, hGg, hGsz, hFl2, hFg2⟩, hev, hn, hstk, hfr⟩
  -- ################ ASSEMBLY ################
  have hAll : WordR main (.seq yP xP) (fun vs => vs = env sp R)
      (fun _ out => ∃ (G : List (ℤ × ℤ)) (F : List (ℤ × ℤ)),
        (out = cvecVal F :: cvecVal G :: env sp R) ∧
        (G.length = sp.S) ∧
        (∀ m < sp.S, G.getD (HvdH.crtIdx sp.ss m) (0,0) = pchunkZ sp.y sp.b sp.N' sp.S (sp.p - sp.b) m) ∧
        (vsz (cvecVal G) ≤ 2 * Big) ∧
        (F.length = sp.S) ∧
        (∀ m < sp.S, F.getD (HvdH.crtIdx sp.ss m) (0,0) = pchunkZ sp.x sp.b sp.N' sp.S (sp.p - sp.b) m))
          (fun _ => ((U + (U + (U + (U + (U + (U + (U + (U))))))) + U) + (U + (U + (U + (U + (U + (U + (U)))))) + U)) + ((U + (U + (U + (U + (U + (U + (U + (U))))))) + U) + (U + (U + (U + (U + (U + (U + (U)))))) + U)))
          :=
    seqGen hKer hy1 hxP
  have hcost34 : ((U + (U + (U + (U + (U + (U + (U + (U))))))) + U) + (U + (U + (U + (U + (U + (U + (U)))))) + U)) + ((U + (U + (U + (U + (U + (U + (U + (U))))))) + U) + (U + (U + (U + (U + (U + (U + (U)))))) + U)) = 34 * U := by ring
  have hcost_le : 34 * U ≤ Kprep * Big := by
    rw [hUeq, hT, hKprep]
    calc 34 * (1000 * (100 * Big) * S₀) = (34 * (1000 * 100)) * (Big * S₀) := by ring
      _ ≤ 1000000000 * (Big * S₀) := Nat.mul_le_mul_right _ (by norm_num)
      _ = 1000000000 * S₀ * Big := by ring
  have hfin3 : Kprep * Big = Kprep * (sp.S + 1) * (vsz (intList sp.ss) + vsz (intList sp.ts) + sp.b + sp.p + 1) * (sp.S.size + 1)
      + Kprep * (sp.S + 1) * (sp.p + 1) * (sp.b + 1) * (HvdH.D + 1)
      + Kprep * (sp.x.size + sp.y.size + sp.b + sp.N' + sp.S + 1)
      + Kprep * (envsz sp + 1) := by
    rw [hKprep, hBig, hA1, hA2, hA3, hA4]
    ring
  refine hKer.conseq main (.seq yP xP) (fun vs => vs = env sp R) (fun vs => vs = env sp R)
    (fun _ out => ∃ (G : List (ℤ × ℤ)) (F : List (ℤ × ℤ)),
      (out = cvecVal F :: cvecVal G :: env sp R) ∧
      (G.length = sp.S) ∧
      (∀ m < sp.S, G.getD (HvdH.crtIdx sp.ss m) (0,0) = pchunkZ sp.y sp.b sp.N' sp.S (sp.p - sp.b) m) ∧
      (vsz (cvecVal G) ≤ 2 * Big) ∧
      (F.length = sp.S) ∧
      (∀ m < sp.S, F.getD (HvdH.crtIdx sp.ss m) (0,0) = pchunkZ sp.x sp.b sp.N' sp.S (sp.p - sp.b) m))
    (fun vs out => (∃ (F G : List (ℤ × ℤ)), vs = env sp R ∧
        out = cvecVal F :: cvecVal G :: env sp R ∧
        F.length = sp.S ∧ G.length = sp.S ∧
        (∀ m < sp.S, F.getD (HvdH.crtIdx sp.ss m) (0,0) = pchunkZ sp.x sp.b sp.N' sp.S (sp.p - sp.b) m) ∧
        (∀ m < sp.S, G.getD (HvdH.crtIdx sp.ss m) (0,0) = pchunkZ sp.y sp.b sp.N' sp.S (sp.p - sp.b) m)))
    (fun _ => ((U + (U + (U + (U + (U + (U + (U + (U))))))) + U) + (U + (U + (U + (U + (U + (U + (U)))))) + U)) + ((U + (U + (U + (U + (U + (U + (U + (U))))))) + U) + (U + (U + (U + (U + (U + (U + (U)))))) + U)))
    (fun _ => Kprep * (sp.S + 1) * (vsz (intList sp.ss) + vsz (intList sp.ts) + sp.b + sp.p + 1) * (sp.S.size + 1)
      + Kprep * (sp.S + 1) * (sp.p + 1) * (sp.b + 1) * (HvdH.D + 1)
      + Kprep * (sp.x.size + sp.y.size + sp.b + sp.N' + sp.S + 1)
      + Kprep * (envsz sp + 1)) hAll ?_ ?_ ?_
  · intro vs hvs; exact hvs
  · intro vs out hvs hq
    obtain ⟨G, F, hout, hGl, hGg, -, hFl, hFg⟩ := hq
    exact ⟨F, G, hvs, hout, hFl, hGl, hFg, hGg⟩
  · intro vs _
    exact le_trans (le_of_eq hcost34) (le_trans hcost_le (le_of_eq hfin3))
end Work.Main.step