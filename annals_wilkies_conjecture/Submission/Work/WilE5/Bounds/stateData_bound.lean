/-
  WilE5 — bounds on the *data* of every state of the fibrewise stratification recursion.

  A state `σ` of the recursion (`Work.WilE5.St`) at level `k` carries
  * a system `σ.B` of equations with pivot directions, whose total degree is measured by
    `Bsum σ.B = ∑ atomDeg (hFun σ.B a)`;
  * a flatness family `σ.Φ`, accumulated vanishing conditions `σ.Ξ` and strict positivity
    conditions `σ.ν`, whose lengths and whose members' `atomDeg` we bound.

  The recursion only *appends* to these four lists, so all these quantities are bounded by an
  explicit function of the level.  Two numbers govern the growth:
  * the cost of one round of fibrewise operators, `q * Mtest * (Bsum σ.B + 1)`
    (`Work.WilE5.Bounds.atomDeg_yOpSt_le`);
  * the number of conditions a child appends, `(prec M NΦ σ t).length`, which is at most
    `σ.Φ.length * (M + 1) ^ q * q` because every element of `prec` is a *valid* test, hence has
    source index `t.i < σ.Φ.length` (`Work.WilE5.Bounds.prec_length_le`).

  In particular the recursion is driven by `σ.Φ.length` and `Bsum σ.B`, *not* by the nominal
  source bound `NΦ`: this is what makes the resulting bound uniform in `NΦ`.  The level factor is
  `Gfac q Mtest = 3 + q * (Mtest + 1) ^ q`, and everything is absorbed into the single explicit
  polynomial `D0poly q` of degree `q ^ 2 + 1` in `Mtest + X.deg`.
-/
import Mathlib
import Submission.Work.WilE5.Sys
import Submission.Work.WilE5.Bounds.atomDeg_yOpSt_le
import Submission.Work.WilE5.Bounds.prec_length_le
import Submission.Work.WilE5.Bounds.Bnd_le_poly
import Submission.Work.WilE5.Strat.stSemiPf_subset_flatSemiPf_union_children

noncomputable section
open WilkiesDesign WilkiesDesign.E
open Work.WilE5

namespace Work.WilE5.Bounds

variable {p q : ℕ}

/-! ## §1. The bound and the invariant -/

/-- Total degree of the equations of a state, written as a list sum.  (`atomDeg_yOpSt_le` uses the
`Fin`-indexed form; `Bsum_eq_sum` converts.) -/
def Bsum {k r : ℕ} {q : ℕ} (B : List (EAPoly k r × Fin q)) : ℕ := (B.map fun p => atomDeg p.1).sum

/-- The growth factor of the state data per level of the recursion. -/
def Gfac (q M : ℕ) : ℕ := 3 + q * (M + 1) ^ q

/-- The bound on the data of a state at level `k` (`D = X.deg`). -/
def Bnd (q M D k : ℕ) : ℕ := (2 * Gfac q M) ^ k * (3 * D + 3 * q + 4)

/-- The invariant: the data of a state at level `k` is bounded by `Bnd q M X.deg k`. -/
def StBnd (X : SemiPf (p + q)) (M k : ℕ) (σ : St p q X.r) : Prop :=
  Bsum σ.B ≤ Bnd q M X.deg k ∧ σ.Φ.length ≤ Bnd q M X.deg k ∧
  σ.Ξ.length ≤ Bnd q M X.deg k ∧ σ.ν.length ≤ Bnd q M X.deg k ∧
  (∀ ψ ∈ σ.Φ, atomDeg ψ ≤ Bnd q M X.deg k) ∧
  (∀ ψ ∈ σ.Ξ, atomDeg ψ ≤ Bnd q M X.deg k) ∧
  (∀ ψ ∈ σ.ν, atomDeg ψ ≤ Bnd q M X.deg k)

/-- The dominating polynomial: `D0poly q` has value `((6+2q)^q * (3q+7)) * (n+1)^(q^2+1)`
at `n`.  (Degree `q ^ 2 + 1` in `n`; its coefficients depend only on `q`.) -/
def D0poly (q : ℕ) : Polynomial ℕ :=
  Polynomial.C ((6 + 2 * q) ^ q * (3 * q + 7)) * (Polynomial.X + 1) ^ (q ^ 2 + 1)

/-! ## §2. Elementary facts -/

/-- The `Fin`-indexed sum of `atomDeg` over a state's system is the list sum `Bsum`. -/
lemma Bsum_eq_sum {p q r : ℕ} (B : List (EAPoly (p + q) r × Fin q)) :
    (∑ a : Fin B.length, atomDeg (hFun B a)) = Bsum B := by
  induction B with
  | nil => simp [Bsum, hFun]
  | cons x B ih =>
    show (∑ a : Fin (B.length + 1), atomDeg (hFun (x :: B) a)) = Bsum (x :: B)
    rw [Fin.sum_univ_succ]
    have h0 : hFun (x :: B) 0 = x.1 := by simp [hFun]
    have hsucc : ∀ i : Fin B.length, hFun (x :: B) i.succ = hFun B i := by
      intro i; simp [hFun]
    rw [h0]
    simp only [hsucc]
    rw [ih]
    simp [Bsum]

lemma qM_le (q M : ℕ) : q * M ≤ q * (M + 1) ^ q := by
  cases q with
  | zero => simp
  | succ n =>
    exact Nat.mul_le_mul_left _ (le_trans (Nat.le_succ M) (Nat.le_self_pow (Nat.succ_ne_zero n) (M+1)))

lemma hG1 (q M : ℕ) : 1 + q * M ≤ Gfac q M := by
  have := qM_le q M; unfold Gfac at *; omega

lemma hGL3 (q M : ℕ) : 3 + (M+1)^q * q ≤ 2 * Gfac q M := by
  have h : (M+1)^q * q = q * (M+1)^q := Nat.mul_comm _ _
  unfold Gfac; rw [h]; omega

lemma hGL2 (q M : ℕ) : 2 + (M+1)^q * q ≤ 2 * Gfac q M := by
  have h : (M+1)^q * q = q * (M+1)^q := Nat.mul_comm _ _
  unfold Gfac; rw [h]; omega

lemma hG5 (q M : ℕ) : 1 + 2 * (q * M) ≤ 2 * Gfac q M := by
  have := qM_le q M; unfold Gfac at *; omega

lemma Bnd_one_le (q M D k : ℕ) : 1 ≤ Bnd q M D k := by
  unfold Bnd
  have h1 : 0 < 2 * Gfac q M := by unfold Gfac; omega
  have h2 : 0 < 3 * D + 3 * q + 4 := by omega
  exact Nat.succ_le_of_lt (Nat.mul_pos (pow_pos h1 k) h2)

lemma Bnd_succ (q M D k : ℕ) : Bnd q M D (k+1) = 2 * Gfac q M * Bnd q M D k := by
  simp only [Bnd, pow_succ]; ring

lemma Bnd_mono {q M D k n : ℕ} (h : k ≤ n) : Bnd q M D k ≤ Bnd q M D n := by
  unfold Bnd
  apply Nat.mul_le_mul_right
  have h0 : (0:ℕ) < 2 * Gfac q M := by unfold Gfac; omega
  exact Nat.pow_le_pow_right h0 h

/-- The level factor absorbs one appended pivot. -/
lemma arith1 (G q M B : ℕ) (hG : 1 + q * M ≤ G) (hB : 1 ≤ B) :
    B + (B + q * M * (B + 1)) ≤ 2 * G * B := by
  have h1 : q * M ≤ q * M * B := by
    calc q * M = q * M * 1 := (Nat.mul_one _).symm
      _ ≤ q * M * B := Nat.mul_le_mul_left _ hB
  have h4 : B + (B + q * M * (B + 1)) = 2 * B + q * M * B + q * M := by ring
  rw [h4]
  calc 2 * B + q * M * B + q * M ≤ 2 * B + q * M * B + q * M * B := by omega
    _ = (2 * B) * (1 + q * M) := by ring
    _ ≤ (2 * B) * G := Nat.mul_le_mul_left _ hG
    _ = 2 * G * B := by ring

lemma arith2 (G L B : ℕ) (hGL : 3 + L ≤ 2 * G) (hB : 1 ≤ B) :
    B + (B + B * L + 1) ≤ 2 * G * B := by
  have h5 : B + (B + B * L + 1) = B * (2 + L) + 1 := by ring
  rw [h5]
  calc B * (2 + L) + 1 ≤ B * (2 + L) + B := by omega
    _ = B * (3 + L) := by ring
    _ ≤ B * (2 * G) := Nat.mul_le_mul_left _ hGL
    _ = 2 * G * B := by ring

lemma arith3 (G L B : ℕ) (hGL : 2 + L ≤ 2 * G) (hB : 1 ≤ B) :
    B + B * L + 1 ≤ 2 * G * B := by
  have h5 : B + B * L + 1 = B * (1 + L) + 1 := by ring
  rw [h5]
  calc B * (1 + L) + 1 ≤ B * (1 + L) + B := by omega
    _ = B * (2 + L) := by ring
    _ ≤ B * (2 * G) := Nat.mul_le_mul_left _ hGL
    _ = 2 * G * B := by ring

lemma arith4 (G B : ℕ) (hG : 1 ≤ G) (hB : 1 ≤ B) : B + 1 ≤ 2 * G * B := by
  have h6 : B ≤ G * B := by
    calc B = 1 * B := (one_mul B).symm
      _ ≤ G * B := Nat.mul_le_mul_right B hG
  calc B + 1 ≤ B + B := by omega
    _ = 2 * B := by ring
    _ ≤ 2 * (G * B) := Nat.mul_le_mul_left 2 h6
    _ = 2 * G * B := by ring

lemma arith5 (G q M B : ℕ) (hG : 1 + 2 * (q * M) ≤ 2 * G) (hB : 1 ≤ B) :
    B + q * M * (B + 1) ≤ 2 * G * B := by
  have h1 : q * M ≤ q * M * B := by
    calc q * M = q * M * 1 := (Nat.mul_one _).symm
      _ ≤ q * M * B := Nat.mul_le_mul_left _ hB
  have h4 : B + q * M * (B + 1) = B + q * M * B + q * M := by ring
  rw [h4]
  calc B + q * M * B + q * M ≤ B + q * M * B + q * M * B := by omega
    _ = B * (1 + 2 * (q * M)) := by ring
    _ ≤ B * (2 * G) := Nat.mul_le_mul_left _ hG
    _ = 2 * G * B := by ring

lemma mSum_mList_le {q M : ℕ} {m : Fin q → ℕ} (hM : ∀ i, m i ≤ M) : mSum m ≤ q * M := by
  unfold mSum
  calc ∑ i : Fin q, m i ≤ ∑ _i : Fin q, M := Finset.sum_le_sum (fun i _ => hM i)
    _ = q * M := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

lemma atomDeg_neg {k r : ℕ} (ψ : EAPoly k r) : atomDeg (-ψ) = atomDeg ψ := by
  simp [atomDeg, MvPolynomial.totalDegree_neg]

lemma Bsum_childB {p q r : ℕ} (c : EAChain (p + q) r) (σ : St p q r) (t : Test q) :
    Bsum (childB c σ t) = Bsum σ.B + atomDeg (peelVal c σ t) := by
  simp [Bsum, childB, List.map_append, List.sum_append]

/-! ## §3. Membership in the appended conditions -/

lemma mem_childΞ_imp {p q r : ℕ} (c : EAChain (p + q) r) (M NΦ : ℕ) (σ : St p q r) (t : Test q)
    (ψ : EAPoly (p + q) r) : ψ ∈ childΞ c M NΦ σ t →
      ψ ∈ σ.Ξ ∨ (∃ t' ∈ prec M NΦ σ t, opVal c σ t' = ψ) ∨ ψ = peelVal c σ t := by
  intro h
  rw [childΞ] at h
  rcases List.mem_append.mp h with h1 | h1
  · rcases List.mem_append.mp h1 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (Or.inl (List.mem_map.mp h2))
  · exact Or.inr (Or.inr (List.mem_singleton.mp h1))

lemma mem_childν_imp {p q r : ℕ} (c : EAChain (p + q) r) (σ : St p q r) (t : Test q) (s : Bool)
    (ψ : EAPoly (p + q) r) : ψ ∈ childν c σ t s →
      ψ ∈ σ.ν ∨ ψ = opVal c σ t ∨ ψ = - opVal c σ t := by
  intro h
  rw [childν] at h
  split at h
  · rcases List.mem_append.mp h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl (List.mem_singleton.mp h1))
  · rcases List.mem_append.mp h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr (List.mem_singleton.mp h1))

lemma prec_subset_testL {p q r : ℕ} (M NΦ : ℕ) (σ : St p q r) (t : Test q) :
    ∀ t' ∈ prec M NΦ σ t, t' ∈ testL q M NΦ :=
  fun t' ht' => List.mem_of_mem_filter ht'

/-! ## §4. The initial states -/

lemma atomDeg_facePoly_le {p q r : ℕ} (l : Fin q) (c : ℝ) :
    atomDeg (facePoly (p := p) (r := r) l c) ≤ 2 := by
  have h : (facePoly (p := p) (r := r) l c).totalDegree ≤ 1 := by
    unfold facePoly
    refine (MvPolynomial.totalDegree_sub _ _).trans ?_
    rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]
    simp
  simp only [atomDeg]
  omega

lemma atomDeg_intPoly_le {p q r : ℕ} (l : Fin q) : atomDeg (intPoly (p := p) (r := r) l) ≤ 3 := by
  have h1 := MvPolynomial.totalDegree_sub (MvPolynomial.C (1:ℝ) : EAPoly (p+q) r)
    (MvPolynomial.X (Sum.inl (yDir p l)) * MvPolynomial.X (Sum.inl (yDir p l)))
  have h2 : (MvPolynomial.C (1:ℝ) : EAPoly (p+q) r).totalDegree ≤ 0 := by simp
  have h3 : (MvPolynomial.X (Sum.inl (yDir p l)) * MvPolynomial.X (Sum.inl (yDir p l)) :
      EAPoly (p+q) r).totalDegree ≤ 2 := by
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_X]
  have h : (intPoly (p := p) (r := r) l).totalDegree ≤ 2 := by
    simp only [intPoly]
    omega
  simp only [atomDeg]
  omega

lemma eqs_sum_le_deg {k r : ℕ} (A : Basic k r) : (A.eqs.map atomDeg).sum ≤ A.deg := by
  simp only [Basic.deg, List.map_append, List.sum_append]
  exact Nat.le_add_right _ _

lemma pos_sum_le_deg {k r : ℕ} (A : Basic k r) : (A.pos.map atomDeg).sum ≤ A.deg := by
  simp only [Basic.deg, List.map_append, List.sum_append]
  exact Nat.le_add_left _ _

lemma list_len_le_sum_atomDeg {k r : ℕ} (L : List (EAPoly k r)) :
    L.length ≤ (L.map atomDeg).sum := by
  have := List.length_le_sum_of_one_le (L.map atomDeg) (fun i hi => by
    obtain ⟨ψ, -, rfl⟩ := List.mem_map.mp hi
    exact atomDeg_pos ψ)
  rwa [List.length_map] at this

lemma mem_atomDeg_le_sum {k r : ℕ} {L : List (EAPoly k r)} {ψ : EAPoly k r} (h : ψ ∈ L) :
    atomDeg ψ ≤ (L.map atomDeg).sum := List.le_sum_of_mem (List.mem_map_of_mem h)

/-- The data of an initial state (a disjunct of `X` together with a cube face pattern) is bounded
by `3 * X.deg + 3 * q + 4 = Bnd q M X.deg 0`. -/
lemma initSt_StBnd {p q : ℕ} (X : SemiPf (p + q)) {A : Basic (p + q) X.r} (hA : A ∈ X.basics)
    (Mtest : ℕ) (Fy : Finset (Fin q)) (ε : {l // l ∈ Fy} → Bool) :
    StBnd X Mtest 0 (initSt X A Fy ε) := by
  have hAdeg : A.deg ≤ X.deg := List.le_sum_of_mem (List.mem_map_of_mem hA)
  have hE : (A.eqs.map atomDeg).sum ≤ X.deg := (eqs_sum_le_deg A).trans hAdeg
  have hP : (A.pos.map atomDeg).sum ≤ X.deg := (pos_sum_le_deg A).trans hAdeg
  have hEl : A.eqs.length ≤ X.deg := (list_len_le_sum_atomDeg A.eqs).trans hE
  have hPl : A.pos.length ≤ X.deg := (list_len_le_sum_atomDeg A.pos).trans hP
  have hEd : ∀ ψ ∈ A.eqs, atomDeg ψ ≤ X.deg := fun ψ hψ => (mem_atomDeg_le_sum hψ).trans hE
  have hPd : ∀ ψ ∈ A.pos, atomDeg ψ ≤ X.deg := fun ψ hψ => (mem_atomDeg_le_sum hψ).trans hP
  have hlen : (Fy.attach.toList).length ≤ q := by
    rw [Finset.length_toList, Finset.card_attach]
    exact (Finset.card_le_univ Fy).trans (le_of_eq (Fintype.card_fin q))
  have hlenc : (Fyᶜ.attach.toList).length ≤ q := by
    rw [Finset.length_toList, Finset.card_attach]
    exact (Finset.card_le_univ Fyᶜ).trans (le_of_eq (Fintype.card_fin q))
  have hBsum : Bsum (initSt X A Fy ε).B ≤ 2 * q := by
    have hmap : Bsum (initSt X A Fy ε).B
        = ((Fy.attach.toList).map
            (fun l => atomDeg (facePoly (p := p) (r := X.r) l.1 (if ε l then 1 else -1)))).sum := by
      simp only [Bsum, initSt, List.map_map]
      rfl
    rw [hmap]
    calc ((Fy.attach.toList).map
            (fun l => atomDeg (facePoly (p := p) (r := X.r) l.1 (if ε l then 1 else -1)))).sum
        ≤ ((Fy.attach.toList).map (fun _ => 2)).sum :=
          List.sum_le_sum (fun x _ => atomDeg_facePoly_le x.1 (if ε x then 1 else -1))
      _ = (Fy.attach.toList).length * 2 := by
          rw [List.map_const', List.sum_replicate, smul_eq_mul]
      _ ≤ q * 2 := Nat.mul_le_mul_right 2 hlen
      _ = 2 * q := by ring
  have hlenν : (initSt X A Fy ε).ν.length ≤ X.deg + q := by
    have h : (initSt X A Fy ε).ν.length = A.pos.length + (Fyᶜ.attach.toList).length := by
      simp [initSt, List.length_append, List.length_map]
    rw [h]
    exact add_le_add hPl hlenc
  have hνd : ∀ ψ ∈ (initSt X A Fy ε).ν, atomDeg ψ ≤ 3 * X.deg + 3 * q + 4 := by
    intro ψ hψ
    simp only [initSt, List.mem_append, List.mem_map] at hψ
    rcases hψ with h1 | ⟨l, -, rfl⟩
    · exact (hPd ψ h1).trans (by omega)
    · exact (atomDeg_intPoly_le l.1).trans (by omega)
  simp only [StBnd, Bnd, pow_zero, one_mul]
  exact ⟨hBsum.trans (by omega), hEl.trans (by omega), hEl.trans (by omega), hlenν.trans (by omega),
    (fun ψ hψ => (hEd ψ hψ).trans (by omega)), (fun ψ hψ => (hEd ψ hψ).trans (by omega)), hνd⟩

/-! ## §5. The recursion step -/

/-- One step of the recursion: the children of a state have their data bounded by the next level's
bound.  Everything a child appends is either an operator value at a *valid* test (whose source index
is `< σ.Φ.length`, whence `prec_length_le`) or a pivot value, and the degree of an appended operator
grows linearly in the current pivot sum (`atomDeg_yOpSt_le`). -/
theorem child_StBnd (X : SemiPf (p + q)) (M NΦ k : ℕ) (σ : St p q X.r)
    (t : Test q) (s : Bool) (hσ : StBnd X M k σ) (ht : t ∈ testL q M NΦ) :
    StBnd X M (k + 1) (childSt X.c M NΦ σ t s) := by
  obtain ⟨hB, hΦ, hΞ, hν, hΦd, hΞd, hνd⟩ := hσ
  have hB1 : 1 ≤ Bnd q M X.deg k := Bnd_one_le ..
  -- the degree of every test source is bounded by the level bound
  have htp : ∀ i, atomDeg (testPoly σ i) ≤ Bnd q M X.deg k := by
    intro i
    by_cases hi : i < σ.Φ.length
    · exact hΦd _ (Work.WilE5.Strat.testPoly_mem σ hi)
    · have hz : testPoly σ i = 0 := by
        simp only [testPoly, List.getElem?_eq_none (Nat.le_of_not_lt hi), Option.getD_none]
      rw [hz]
      simp only [atomDeg, MvPolynomial.totalDegree_zero, Nat.zero_add]
      exact hB1
  -- the degree of an operator value at a test of `testL`
  have hopAny : ∀ t' ∈ testL q M NΦ,
      atomDeg (opVal X.c σ t') ≤ Bnd q M X.deg k + q * M * (Bnd q M X.deg k + 1) := by
    intro t' ht'
    have ht'L := (Work.WilE5.Strat.mem_testL_iff t').mp ht'
    have hM' : ∀ i, t'.m i ≤ M := (mem_mList_iff t'.m).mp ht'L.2.1
    have htm' : mSum t'.m ≤ q * M := mSum_mList_le hM'
    have h := atomDeg_yOpSt_le X σ (testPoly σ t'.i) t'.m
    rw [Bsum_eq_sum σ.B] at h
    exact h.trans (add_le_add (htp t'.i) (Nat.mul_le_mul htm' (Nat.succ_le_succ hB)))
  -- the degree of the appended pivot (the peeled operator)
  have hpeel : atomDeg (peelVal X.c σ t) ≤ Bnd q M X.deg k + q * M * (Bnd q M X.deg k + 1) := by
    have htL := (Work.WilE5.Strat.mem_testL_iff t).mp ht
    have hsm : mSum (mDec t.m t.l) ≤ q * M :=
      mSum_mList_le ((mem_mList_iff _).mp (mDec_mem_mList htL.2.1 t.l))
    have h := atomDeg_yOpSt_le X σ (testPoly σ t.i) (mDec t.m t.l)
    rw [Bsum_eq_sum σ.B] at h
    exact h.trans (add_le_add (htp t.i) (Nat.mul_le_mul hsm (Nat.succ_le_succ hB)))
  have hop := hopAny t ht
  -- the number of conditions a child appends is bounded by the size of the flatness family
  have hprec : (prec M NΦ σ t).length ≤ Bnd q M X.deg k * ((M+1)^q * q) := by
    refine (prec_length_le M NΦ σ t).trans ?_
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ hΦ
  have key : Bnd q M X.deg k ≤ 2 * Gfac q M * Bnd q M X.deg k := by
    have h2 : 1 ≤ 2 * Gfac q M := by unfold Gfac; omega
    calc Bnd q M X.deg k = 1 * Bnd q M X.deg k := (one_mul _).symm
      _ ≤ (2 * Gfac q M) * Bnd q M X.deg k := Nat.mul_le_mul_right _ h2
  have key2 := arith5 (Gfac q M) q M (Bnd q M X.deg k) (hG5 q M) hB1
  have hlenΞ : (childΞ X.c M NΦ σ t).length
      ≤ Bnd q M X.deg k + Bnd q M X.deg k * ((M+1)^q * q) + 1 := by
    have h0 : (childΞ X.c M NΦ σ t).length = (σ.Ξ.length + (prec M NΦ σ t).length) + 1 := by
      simp only [childΞ, List.length_append, List.length_map, List.length_singleton]
    rw [h0]
    exact Nat.add_le_add_right (add_le_add hΞ hprec) 1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Bnd_succ, show (childSt X.c M NΦ σ t s).B = childB X.c σ t from rfl, Bsum_childB]
    exact (add_le_add hB hpeel).trans (arith1 _ _ _ _ (hG1 q M) hB1)
  · rw [Bnd_succ]
    have h1 : (childSt X.c M NΦ σ t s).Φ.length = σ.Φ.length + (childΞ X.c M NΦ σ t).length := by
      simp [childSt]
    rw [h1]
    exact (add_le_add hΦ hlenΞ).trans (arith2 _ _ _ (hGL3 q M) hB1)
  · rw [Bnd_succ]
    exact hlenΞ.trans (arith3 _ _ _ (hGL2 q M) hB1)
  · rw [Bnd_succ]
    have h1 : (childSt X.c M NΦ σ t s).ν.length = σ.ν.length + 1 := by
      simp only [childSt, childν, List.length_append, List.length_singleton]
      split <;> simp
    rw [h1]
    exact (Nat.succ_le_succ hν).trans (arith4 _ _ (by unfold Gfac; omega) hB1)
  · rw [Bnd_succ]
    intro ψ hψ
    have hmem : ψ ∈ σ.Φ ∨ ψ ∈ childΞ X.c M NΦ σ t := by
      simpa [childSt] using hψ
    rcases hmem with h1 | h1
    · exact (hΦd ψ h1).trans key
    · rcases mem_childΞ_imp X.c M NΦ σ t ψ h1 with h2 | ⟨t', ht'p, ht'⟩ | h2
      · exact (hΞd ψ h2).trans key
      · rw [← ht']; exact (hopAny t' (prec_subset_testL M NΦ σ t t' ht'p)).trans key2
      · rw [h2]; exact hpeel.trans key2
  · rw [Bnd_succ]
    intro ψ hψ
    rcases mem_childΞ_imp X.c M NΦ σ t ψ hψ with h2 | ⟨t', ht'p, ht'⟩ | h2
    · exact (hΞd ψ h2).trans key
    · rw [← ht']; exact (hopAny t' (prec_subset_testL M NΦ σ t t' ht'p)).trans key2
    · rw [h2]; exact hpeel.trans key2
  · rw [Bnd_succ]
    intro ψ hψ
    rcases mem_childν_imp X.c σ t s ψ hψ with h1 | h1 | h1
    · exact (hνd ψ h1).trans key
    · rw [h1]; exact hop.trans key2
    · rw [h1, atomDeg_neg]; exact hop.trans key2

/-! ## §6. The invariant holds at every level -/

theorem level_StBnd {p q : ℕ} (X : SemiPf (p + q)) (M NΦ : ℕ) :
    ∀ k, ∀ σ ∈ level X M NΦ k, StBnd X M k σ := by
  intro k
  induction k with
  | zero =>
    intro σ hσ
    have hσ' : σ ∈ initStates X := hσ
    obtain ⟨A, hA, Fy, ε, rfl⟩ := exists_of_mem_initStates X hσ'
    exact initSt_StBnd X hA M Fy ε
  | succ k ih =>
    intro σ' hσ'
    have hσ'' : σ' ∈ (level X M NΦ k).flatMap (fun σ => children X.c M NΦ σ) := hσ'
    obtain ⟨σ, hσ, hc⟩ := List.mem_flatMap.mp hσ''
    obtain ⟨t, ht, hc2⟩ := List.mem_flatMap.mp hc
    rcases List.mem_cons.mp hc2 with h | h
    · rw [h]
      exact child_StBnd X M NΦ k σ t false (ih σ hσ) ht
    · rw [List.mem_singleton.mp h]
      exact child_StBnd X M NΦ k σ t true (ih σ hσ) ht

/-! ## §7. The bound -/

/-- Every state of the recursion (all levels `≤ q`) has its data — the total degree of the pivot
functions, the number and the degrees of the flatness sources, and the degrees of the equations and
of the strict conditions — bounded by one polynomial evaluated at `Mtest + X.deg`, *uniformly in
`X`, `Mtest`, `NΦ`* (the polynomial depends only on `q ≤ F`; note `D0` must not depend on `Mtest`,
`NΦ` or `X`, otherwise the statement is vacuous).

This is the input for choosing the uniform test bound `Mtest` and the source bound `NΦ` in the
assembly of `E5_strat`, and for the degree bound on each produced stratum.

Suggested route: each child only *appends* to `B`, `Ξ`, `Φ`, `ν`:
`childB = σ.B ++ [(peelVal, t.l)]`, `childΞ = σ.Ξ ++ (prec …).map (opVal …) ++ [peelVal]`,
`childν = σ.ν ++ [± opVal t]`, `Φ' = Φ ++ Ξ'`.  Bound the degree of an appended operator by
`Work.WilE5.Bounds.atomDeg_yOpSt_le` (applied with `mSum m ≤ q * Mtest`, since `m ∈ mList q Mtest`
has entries `≤ Mtest`), and the number of appended conditions by
`1 + |prec| ≤ 1 + |testL q Mtest NΦ| ≤ 1 + NΦ * (Mtest + 1) ^ q * q`.
The initial states (`Work.WilE5.initStates`) have `Ξ = Φ = A.eqs` with `A ∈ X.basics` (at most
`X.deg` atoms of degree `≤ X.deg`), the face equations of degree `1` as pivots, and `A.pos` plus the
interior inequalities in `ν`.  The pivot-degree recurrence is linear:
`S' = S + atomDeg (peelVal) ≤ S + A + q * Mtest * (S + 1)`, giving
`S ≤ (1 + q * Mtest) ^ q * (X.deg + 1)` after `q` levels; absorb everything into a single explicit
polynomial `D0` in `Mtest + X.deg` (prove the inequalities polynomially — no `decide`/`norm_num` on
concrete constants). -/
theorem stateData_bound {p q : ℕ} :
    ∃ D0 : Polynomial ℕ, ∀ (X : WilkiesDesign.E.SemiPf (p + q)) (Mtest NΦ : ℕ),
      ∀ k ∈ Finset.range (q + 1), ∀ σ ∈ Work.WilE5.level X Mtest NΦ k,
      (∑ a : Fin σ.B.length, WilkiesDesign.E.atomDeg (Work.WilE5.hFun σ.B a)) ≤
        D0.eval (Mtest + X.deg) ∧
      σ.Φ.length ≤ D0.eval (Mtest + X.deg) ∧
      (∀ ψ ∈ σ.Φ, WilkiesDesign.E.atomDeg ψ ≤ D0.eval (Mtest + X.deg)) ∧
      (∀ ψ ∈ σ.ν, WilkiesDesign.E.atomDeg ψ ≤ D0.eval (Mtest + X.deg)) ∧
      (∀ ψ ∈ σ.Ξ, WilkiesDesign.E.atomDeg ψ ≤ D0.eval (Mtest + X.deg)) := by
  refine ⟨D0poly q, ?_⟩
  intro X Mtest NΦ k hk σ hσ
  have hkq : k ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  obtain ⟨hB, hΦ, hΞ, hν, hΦd, hΞd, hνd⟩ := level_StBnd X Mtest NΦ k σ hσ
  have hmono : Bnd q Mtest X.deg k ≤
      ((6 + 2 * q) ^ q * (3 * q + 7)) * (Mtest + X.deg + 1) ^ (q ^ 2 + 1) :=
    (Bnd_mono hkq).trans Bnd_le_poly
  have hD0 : Polynomial.eval (Mtest + X.deg) (D0poly q) =
      ((6 + 2 * q) ^ q * (3 * q + 7)) * (Mtest + X.deg + 1) ^ (q ^ 2 + 1) := by
    simp [D0poly]
  rw [hD0]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Bsum_eq_sum σ.B]; exact hB.trans hmono
  · exact hΦ.trans hmono
  · exact fun ψ hψ => (hΦd ψ hψ).trans hmono
  · exact fun ψ hψ => (hνd ψ hψ).trans hmono
  · exact fun ψ hψ => (hΞd ψ hψ).trans hmono

end Work.WilE5.Bounds
