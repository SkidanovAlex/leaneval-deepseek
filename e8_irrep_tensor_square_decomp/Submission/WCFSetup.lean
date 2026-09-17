import Submission.E8Ball
import Submission.E8CharCompute
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_wactMat_finite
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_wact_sign_rho
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_wact_fixes_strict_dominant
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_dom_sub_wact_mem_cone

/-!
# Setting up the Weyl character formula

This file builds the Weyl group of `E₈` as a *finite set of matrices* (from the commons lemma
`E8_wactMat_finite`), its sign function (`det`, well defined by `E8_wact_sign_rho`), the Weyl sum
`WSum f x = ∑_{w ∈ W} ε(w) f (x - wρ)` of a function, and the statement of the Weyl character
formula for `V = L(ω₁+ω₈)`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace Submission.WCFSetup

open Commons.LinearAlgebra.Matrix.Cartan

/-- The Weyl group of `E₈`, as the finite set of matrices of the elements `wact L`. -/
noncomputable def WG : Finset (Matrix (Fin 8) (Fin 8) ℤ) :=
  Commons.LinearAlgebra.Matrix.Cartan.E8_wactMat_finite.toFinset

lemma mem_WG {M : Matrix (Fin 8) (Fin 8) ℤ} : M ∈ WG ↔ ∃ L : List (Fin 8), wactMat L = M := by
  simp [WG, Set.Finite.mem_toFinset, Set.mem_range]

lemma wactMat_mem (L : List (Fin 8)) : wactMat L ∈ WG := mem_WG.mpr ⟨L, rfl⟩

/-- The matrix of `wact L` acts on vectors as `wact L`. -/
lemma wactMat_mulVec (L : List (Fin 8)) (v : Fin 8 → ℤ) : (wactMat L).mulVec v = wact L v := by
  have h : wact L v = ∑ b, v b • wact L (Pi.single b (1 : ℤ)) := by
    conv_lhs => rw [eq_sum_smul_single v]
    rw [wact_sum_smul]
  rw [h]
  funext a
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, wactMat]
  exact Finset.sum_congr rfl (fun b _ => mul_comm _ _)

lemma wactMat_singleton (i : Fin 8) : wactMat [i] = srefMat i := by
  rw [show ([i] : List (Fin 8)) = i :: [] from rfl, wactMat_cons, wactMat_nil, Matrix.one_mul]

/-- The matrix of an involutive reflection is an involution. -/
lemma srefMat_mul_self (i : Fin 8) : srefMat i * srefMat i = 1 := by
  have h : wactMat [i, i] = srefMat i * srefMat i := by
    rw [show ([i, i] : List (Fin 8)) = i :: [i] from rfl, wactMat_cons, wactMat_singleton]
  rw [← h]
  ext a b
  simp only [wactMat, Matrix.one_apply]
  rw [show ([i, i] : List (Fin 8)) = [i] ++ [i] from rfl, wact_append, wact_singleton,
    wact_singleton, sref_invol]
  simp [Pi.single_apply]

/-- Appending a single reflection on the right multiplies the matrix on the left. -/
lemma wactMat_append_single (i : Fin 8) (L : List (Fin 8)) :
    wactMat (L ++ [i]) = srefMat i * wactMat L := by
  induction L with
  | nil => rw [List.nil_append, wactMat_singleton, wactMat_nil, Matrix.mul_one]
  | cons j L ih =>
      rw [show (j :: L) ++ [i] = j :: (L ++ [i]) from rfl, wactMat_cons, ih, wactMat_cons,
        Matrix.mul_assoc]

/-- Multiplication of matrices along concatenation of words. -/
lemma wactMat_append (L₁ L₂ : List (Fin 8)) :
    wactMat (L₁ ++ L₂) = wactMat L₂ * wactMat L₁ := by
  induction L₂ generalizing L₁ with
  | nil => rw [List.append_nil, wactMat_nil, Matrix.one_mul]
  | cons i L ih =>
      have hassoc : L₁ ++ (i :: L) = (L₁ ++ [i]) ++ L := by rw [List.append_assoc]; rfl
      rw [hassoc, ih, wactMat_append_single, wactMat_cons, Matrix.mul_assoc]

/-- Reversing a word inverts its Weyl group element. -/
lemma wactMat_mul_reverse (L : List (Fin 8)) : wactMat L * wactMat L.reverse = 1 := by
  induction L with
  | nil => rw [List.reverse_nil, wactMat_nil, Matrix.mul_one]
  | cons i L ih =>
      rw [List.reverse_cons, wactMat_append_single, wactMat_cons, Matrix.mul_assoc,
        ← Matrix.mul_assoc (srefMat i), srefMat_mul_self, Matrix.one_mul, ih]

lemma wactMat_reverse_mul (L : List (Fin 8)) : wactMat L.reverse * wactMat L = 1 := by
  induction L with
  | nil => rw [List.reverse_nil, wactMat_nil, Matrix.mul_one]
  | cons i L ih =>
      rw [List.reverse_cons, wactMat_append_single, wactMat_cons,
        Matrix.mul_assoc (srefMat i) (wactMat L.reverse) (wactMat L * srefMat i),
        ← Matrix.mul_assoc (wactMat L.reverse) (wactMat L) (srefMat i), ih, Matrix.one_mul,
        srefMat_mul_self]

lemma WG_one : (1 : Matrix (Fin 8) (Fin 8) ℤ) ∈ WG := by
  simpa [wactMat_nil] using wactMat_mem ([] : List (Fin 8))

/-- The Weyl group is closed under multiplication. -/
lemma WG_mul {M N : Matrix (Fin 8) (Fin 8) ℤ} (hM : M ∈ WG) (hN : N ∈ WG) : M * N ∈ WG := by
  obtain ⟨L, rfl⟩ := mem_WG.mp hM
  obtain ⟨L', rfl⟩ := mem_WG.mp hN
  exact mem_WG.mpr ⟨L' ++ L, wactMat_append L' L⟩

/-- Every element of the Weyl group has an inverse in the Weyl group. -/
lemma WG_inv {M : Matrix (Fin 8) (Fin 8) ℤ} (hM : M ∈ WG) :
    ∃ N ∈ WG, M * N = 1 ∧ N * M = 1 := by
  obtain ⟨L, rfl⟩ := mem_WG.mp hM
  exact ⟨_, wactMat_mem _, wactMat_mul_reverse L, wactMat_reverse_mul L⟩

/-- The action of a Weyl group element on a weight. -/
noncomputable def ap (M : Matrix (Fin 8) (Fin 8) ℤ) (v : Fin 8 → ℤ) : Fin 8 → ℤ := M.mulVec v

@[simp] lemma ap_mulVec (M : Matrix (Fin 8) (Fin 8) ℤ) (v : Fin 8 → ℤ) : ap M v = M.mulVec v := rfl

lemma wactMat_ap (L : List (Fin 8)) (v : Fin 8 → ℤ) : ap (wactMat L) v = wact L v :=
  wactMat_mulVec L v

@[simp] lemma ap_add (M : Matrix (Fin 8) (Fin 8) ℤ) (a b : Fin 8 → ℤ) :
    ap M (a + b) = ap M a + ap M b := Matrix.mulVec_add M a b

@[simp] lemma ap_one (v : Fin 8 → ℤ) : ap 1 v = v := Matrix.one_mulVec v

@[simp] lemma ap_mul (M N : Matrix (Fin 8) (Fin 8) ℤ) (v : Fin 8 → ℤ) :
    ap (M * N) v = ap M (ap N v) := (Matrix.mulVec_mulVec v M N).symm

/-- The Weyl vector as a vector. -/
noncomputable def rhoV : Fin 8 → ℤ := fun _ => 1

lemma rhoV_eq : rhoV = rhoZ := rfl

/-- **The Weyl sum** of a function: `∑_{w ∈ W} ε(w) f (x - wρ)`. -/
noncomputable def WSum (f : (Fin 8 → ℤ) → ℚ) (x : Fin 8 → ℤ) : ℚ :=
  ∑ M ∈ WG, (M.det : ℚ) * f (x - ap M rhoV)


section Reindex

variable {f : (Fin 8 → ℤ) → ℚ}

/-- **Reindexing the Weyl sum.**  If `f` is invariant under the Weyl group, then
`WSum f (w x) = ε(w) · WSum f x`. -/
lemma WSum_reindex (hf : ∀ M ∈ WG, ∀ y : Fin 8 → ℤ, f (ap M y) = f y)
    (x : Fin 8 → ℤ) (M₀ : Matrix (Fin 8) (Fin 8) ℤ) (h₀ : M₀ ∈ WG) :
    WSum f (ap M₀ x) = (M₀.det : ℚ) * WSum f x := by
  obtain ⟨M₀', hM₀', h₁, h₂⟩ := WG_inv h₀
  rw [WSum, WSum, Finset.mul_sum]
  refine Finset.sum_bij (fun M _ => M₀' * M) ?_ ?_ ?_ ?_
  · intro M hM
    exact WG_mul hM₀' hM
  · intro M₁ h₁' M₂ h₂' heq
    have := congrArg (fun N : Matrix (Fin 8) (Fin 8) ℤ => M₀ * N) heq
    simpa only [← Matrix.mul_assoc, h₁, Matrix.one_mul] using this
  · intro N hN
    exact ⟨M₀ * N, WG_mul h₀ hN, by rw [← Matrix.mul_assoc, h₂, Matrix.one_mul]⟩
  · intro M hM
    have hMM : M₀ * (M₀' * M) = M := by rw [← Matrix.mul_assoc, h₁, Matrix.one_mul]
    have hsplit : ap M₀ x - ap M rhoV = ap M₀ (x - ap (M₀' * M) rhoV) := by
      have h1'' : ap M rhoV = ap M₀ (ap (M₀' * M) rhoV) := by
        conv_lhs => rw [hMM.symm]
        rw [ap_mul]
      rw [h1'']
      simp only [ap_mulVec, Matrix.mulVec_sub]
    have hdet : (((M₀ * (M₀' * M)).det : ℤ) : ℚ) = (M₀.det : ℚ) * ((M₀' * M).det : ℚ) := by
      rw [Matrix.det_mul]; push_cast; ring
    have hdet2 : (((M₀' * M).det : ℤ) : ℚ) * (M₀.det : ℚ) = (M.det : ℚ) := by
      have h : (M₀.det : ℚ) * (((M₀' * M).det : ℤ) : ℚ) = (M.det : ℚ) := by
        have h0 : (((M₀ * (M₀' * M)).det : ℤ) : ℚ) = (M.det : ℚ) := by rw [hMM]
        rw [← h0, hdet]
      rw [mul_comm, h]
    rw [hsplit, hf M₀ h₀ (x - ap (M₀' * M) rhoV), ← hdet2]
    ring

/-- **The Weyl sum of a Weyl-invariant function is anti-invariant.** -/
lemma WSum_anti (hf : ∀ M ∈ WG, ∀ y : Fin 8 → ℤ, f (ap M y) = f y)
    (x : Fin 8 → ℤ) (L : List (Fin 8)) :
    WSum f (wact L x) = (((-1 : ℤ) ^ L.length : ℤ) : ℚ) * WSum f x := by
  have h := WSum_reindex hf x (wactMat L) (wactMat_mem L)
  rwa [wactMat_ap, wactMat_det] at h

/-- Applying the reversed word undoes the action of the word. -/
lemma wact_reverse_wact (L : List (Fin 8)) (v : Fin 8 → ℤ) : wact L.reverse (wact L v) = v := by
  conv_lhs => rw [← wactMat_mulVec L v]
  rw [← wactMat_mulVec L.reverse ((wactMat L).mulVec v), Matrix.mulVec_mulVec, wactMat_reverse_mul,
    Matrix.one_mulVec]

/-- Applying the word undoes the action of the reversed word. -/
lemma wact_wact_reverse (L : List (Fin 8)) (v : Fin 8 → ℤ) : wact L (wact L.reverse v) = v := by
  conv_lhs => rw [← wactMat_mulVec L.reverse v]
  rw [← wactMat_mulVec L ((wactMat L.reverse).mulVec v), Matrix.mulVec_mulVec, wactMat_mul_reverse,
    Matrix.one_mulVec]

/-- **Two words agreeing on the Weyl vector define the same matrix.**  This uses that the stabiliser
of `ρ` in the Weyl group is trivial (`E8_weyl_stab_rho_trivial`). -/
lemma wactMat_eq_of_rho_eq {L L' : List (Fin 8)} (h : wact L rhoZ = wact L' rhoZ) :
    wactMat L = wactMat L' := by
  have hfix : wact (L ++ L'.reverse) rhoZ = rhoZ := by
    rw [wact_append, h]
    exact wact_reverse_wact L' rhoZ
  have hid : ∀ v : Fin 8 → ℤ, wact (L ++ L'.reverse) v = v :=
    E8_weyl_stab_rho_trivial (L ++ L'.reverse) hfix
  have hmat : wactMat (L ++ L'.reverse) = 1 := by
    ext a b
    have h1 := hid (Pi.single b (1 : ℤ))
    show wact (L ++ L'.reverse) (Pi.single b (1 : ℤ)) a = (1 : Matrix (Fin 8) (Fin 8) ℤ) a b
    rw [h1, Matrix.one_apply, Pi.single_apply]
  have h2 : wactMat L'.reverse * wactMat L = 1 := by
    rw [← wactMat_append]; exact hmat
  have h3 : (wactMat L' * wactMat L'.reverse) * wactMat L = wactMat L' := by
    rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  rw [wactMat_mul_reverse, Matrix.one_mul] at h3
  exact h3

end Reindex

section Ball

open Submission.E8Ball

/-- The matrix attached to a ball entry. -/
noncomputable def ballMat (p : (Fin 8 → ℤ) × List (Fin 8)) : Matrix (Fin 8) (Fin 8) ℤ := wactMat p.2

lemma ballMat_mem (p : (Fin 8 → ℤ) × List (Fin 8)) : ballMat p ∈ WG := wactMat_mem p.2

/-- Two ball entries with the same matrix are equal. -/
lemma ballMat_injOn {p q : (Fin 8 → ℤ) × List (Fin 8)} (hp : p ∈ e8ball) (hq : q ∈ e8ball)
    (h : ballMat p = ballMat q) : p = q := by
  have hv : p.1 = q.1 := by
    have h' : (wactMat p.2).mulVec rhoZ = (wactMat q.2).mulVec rhoZ := by
      rw [show wactMat p.2 = wactMat q.2 from h]
    rw [← (e8ball_prop p hp).2, ← (e8ball_prop q hq).2, ← wactMat_mulVec, ← wactMat_mulVec]
    exact h'
  exact List.inj_on_of_nodup_map e8ball_nodup hp hq hv

/-- The set of matrices of the ball of radius `4`. -/
noncomputable def ballSet : Finset (Matrix (Fin 8) (Fin 8) ℤ) := (e8ball.map ballMat).toFinset

lemma mem_ballSet {M : Matrix (Fin 8) (Fin 8) ℤ} :
    M ∈ ballSet ↔ ∃ p ∈ e8ball, ballMat p = M := by
  simp [ballSet]

lemma ballSet_sub : ballSet ⊆ WG := by
  intro M hM
  obtain ⟨p, -, rfl⟩ := mem_ballSet.mp hM
  exact ballMat_mem p

/-- **The Weyl sum equals the sum over the matrices of the certified ball**, provided every word of
length at least `5` gives a vanishing term. -/
theorem WSum_eq_sum_ballSet (f : (Fin 8 → ℤ) → ℚ) (x : Fin 8 → ℤ)
    (hL : ∀ L : List (Fin 8), 5 ≤ L.length → f (x - wact L rhoZ) = 0) :
    WSum f x = ∑ M ∈ ballSet, (M.det : ℚ) * f (x - ap M rhoV) := by
  have hzero : ∀ M ∈ WG, M ∉ ballSet → (M.det : ℚ) * f (x - ap M rhoV) = 0 := by
    intro M hM hMB
    obtain ⟨L, hLw⟩ := mem_WG.mp hM
    have hlen : 5 ≤ L.length := by
      by_contra hc
      have h4 : L.length ≤ 4 := by omega
      obtain ⟨a, ha⟩ := Submission.E8Ball.wact_mem L h4
      have hEq : ballMat (e8ball[a]) = wactMat L := by
        apply wactMat_eq_of_rho_eq
        rw [(e8ball_prop (e8ball[a]) (List.get_mem e8ball a)).2, ha]
      exact hMB (mem_ballSet.mpr ⟨e8ball[a], List.get_mem _ _, hEq.trans hLw⟩)
    have hterm : f (x - ap M rhoV) = 0 := by
      have hap : ap M rhoV = wact L rhoZ := by rw [← hLw, wactMat_ap, rhoV_eq]
      rw [hap]
      exact hL L hlen
    rw [hterm, mul_zero]
  rw [WSum]
  exact (Finset.sum_subset ballSet_sub hzero).symm

/-- The sum over the ball matrices is the sum computed by `Submission.E8CharCompute`. -/
theorem sum_ballSet_eq_ballSum (f : (Fin 8 → ℤ) → ℚ) (x : Fin 8 → ℤ) :
    (∑ M ∈ ballSet, (M.det : ℚ) * f (x - ap M rhoV))
      = (e8ball.map (fun p => (-1 : ℚ) ^ p.2.length * f (x - p.1))).sum := by
  have hNodup : (e8ball.map ballMat).Nodup :=
    (e8ball_nodup.of_map Prod.fst).map_on (fun p hp q hq h => ballMat_injOn hp hq h)
  rw [ballSet, List.sum_toFinset (fun M => (M.det : ℚ) * f (x - ap M rhoV)) hNodup,
    List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  simp only [Function.comp_apply, ballMat, wactMat_ap, wactMat_det, rhoV_eq,
    (e8ball_prop p hp).2]
  push_cast
  ring

/-- **The Weyl sum of `f` at `x` is the certified ball sum.** -/
theorem WSum_eq_ballSum (f : (Fin 8 → ℤ) → ℚ) (x : Fin 8 → ℤ)
    (hL : ∀ L : List (Fin 8), 5 ≤ L.length → f (x - wact L rhoZ) = 0) :
    WSum f x = (e8ball.map (fun p => (-1 : ℚ) ^ p.2.length * f (x - p.1))).sum := by
  rw [WSum_eq_sum_ballSet f x hL, sum_ballSet_eq_ballSum]

/-- **Variant of `WSum_eq_sum_ballSet` with an element-based vanishing hypothesis.**  This is the
form used for `f = mfun`: for a Weyl group element outside the ball (i.e. one with no word of length
`≤ 4`) the support estimate `qq (μ + ρ - wρ) ≥ 2·e8ht(ρ - wρ) ≥ 12 > 10` shows that the term
vanishes.  (The word-based hypothesis above is stronger and is not directly available for `mfun`,
since a long word may represent a short element.) -/
theorem WSum_eq_sum_ballSet' (f : (Fin 8 → ℤ) → ℚ) (x : Fin 8 → ℤ)
    (hvan : ∀ M ∈ WG, M ∉ ballSet → (M.det : ℚ) * f (x - ap M rhoV) = 0) :
    WSum f x = ∑ M ∈ ballSet, (M.det : ℚ) * f (x - ap M rhoV) := by
  rw [WSum]
  exact (Finset.sum_subset ballSet_sub hvan).symm

theorem WSum_eq_ballSum' (f : (Fin 8 → ℤ) → ℚ) (x : Fin 8 → ℤ)
    (hvan : ∀ M ∈ WG, M ∉ ballSet → (M.det : ℚ) * f (x - ap M rhoV) = 0) :
    WSum f x = (e8ball.map (fun p => (-1 : ℚ) ^ p.2.length * f (x - p.1))).sum := by
  rw [WSum_eq_sum_ballSet' f x hvan, sum_ballSet_eq_ballSum]


end Ball

end Submission.WCFSetup
