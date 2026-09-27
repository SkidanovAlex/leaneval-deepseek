import Mathlib
import Submission.Work.Mostow.gapA.defs
import Submission.Work.Mostow.pairStabDefs
import Submission.Work.Mostow.gapA.mem_geodSet_iff_span
import Submission.Work.Mostow.gapA.geodFacts
import Submission.Work.Mostow.gapA.geodEquiv
import Submission.Work.Mostow.ematSpec
import Submission.Work.Mostow.ematFix
import Submission.Work.Mostow.bdFixIff
import Submission.Work.Mostow.HaarBoost
import Submission.Work.Mostow.gapA.orth_det_one_fixedVec
import Submission.Work.Mostow.boundedOrbitFixed
import Submission.Work.Mostow.fix_zero_is_euclidean
import Submission.Work.Mostow.gapA.ematMulDet

set_option maxHeartbeats 1000000

/-!
# The axis of a finite-order orientation-preserving element of `PO 3 1`

A finite-order isometry `f ≠ 1` of `ℍ³` which preserves the orientation is elliptic: its fixed
set is exactly a geodesic `geodSet a b` with `a ≠ b` two boundary points.

Route: `boundedOrbitFixed` produces a fixed point `p` of `f`; conjugating by the boost carrying
the base point to `p` produces an element `g` fixing the base point.  `ematZeroBlock_aux` shows
that `emat g` is block diagonal `fromBlocks S 0 0 1` with `Sᵀ S = 1` and `S.det = det (emat g)`;
`ematMulDet` shows that the latter equals `det (emat f) > 0`, so `det S = 1` and
`so3FixedLine_aux` (from `orth_det_one_fixedVec` plus the rank-one determinant formula) exhibits
the fixed line of `S`.  The axis is then transported back by `geodEquiv`.
-/

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open _root_.Matrix

noncomputable section

variable {n : ℕ}

lemma smul_coe (c : ℝ) (x : E n) (i : Fin n) : (c • x) i = c * x i := rfl

lemma neg_coe (x : E n) (i : Fin n) : (-x) i = - x i := rfl

/-! ## The geodesic through the origin in the direction `a` -/

/-- The geodesic with endpoints `a` and `-a` is the straight line `ℝ a`. -/
theorem geodSetAxis_aux (a : E n) (ha : a ∈ Sph n) :
    ∀ u : E n, u ∈ geodSet a (-a) ↔ ∃ c : ℝ, u = c • a := by
  have hnorm : ‖a‖ = 1 := (mem_Sph_iff a).mp ha
  have hneg : -a ∈ Sph n := by
    rw [mem_Sph_iff, norm_neg]; exact hnorm
  have hane : a ≠ -a := by
    intro h
    have h3 : a + a = 0 := by
      nth_rewrite 2 [h]
      exact add_neg_cancel a
    have h4 : (2 : ℝ) • a = 0 := by rw [two_smul]; exact h3
    have h5 : a = 0 := by
      rcases (smul_eq_zero.mp h4) with h6 | h6
      · exact absurd h6 (by norm_num)
      · exact h6
    rw [h5] at hnorm
    exact absurd hnorm (by simp)
  intro u
  rw [mem_geodSet_iff_span a (-a) ha hneg hane u]
  constructor
  · rintro ⟨α, β, hαβ⟩
    refine ⟨α - β, ?_⟩
    ext i
    have h := congrFun hαβ (Sum.inl i)
    simp only [hlift, nvec, Sum.elim_inl] at h
    rw [h]
    simp only [Pi.add_apply, Pi.smul_apply, Sum.elim_inl, smul_coe, neg_coe]
    ring
  · rintro ⟨c, rfl⟩
    refine ⟨(tpart (c • a) + c) / 2, (tpart (c • a) - c) / 2, ?_⟩
    funext z
    rcases z with i | i
    · simp only [hlift, nvec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Sum.elim_inl,
        smul_coe, neg_coe]
      ring
    · simp only [hlift, nvec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Sum.elim_inr]
      ring

/-! ## Positive definiteness of the dot product on `Fin 3 → ℝ` -/

lemma dotProduct_self_ne_zero {x : Fin 3 → ℝ} (hx : x ≠ 0) : x ⬝ᵥ x ≠ 0 := by
  intro h
  apply hx
  funext i
  rw [dotProduct] at h
  have hsum : ∀ j ∈ (Finset.univ : Finset (Fin 3)), (0 : ℝ) ≤ x j * x j :=
    fun j _ => mul_self_nonneg _
  have h0 : x i * x i = 0 := (Finset.sum_eq_zero_iff_of_nonneg hsum).mp h i (Finset.mem_univ i)
  exact mul_self_eq_zero.mp h0

lemma dot_single (i j : Fin 3) :
    (Pi.single i (1 : ℝ) : Fin 3 → ℝ) ⬝ᵥ (Pi.single j (1 : ℝ)) = (if i = j then (1 : ℝ) else 0) := by
  rw [dotProduct]
  by_cases hij : i = j
  · subst hij
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · intro h; exact absurd (Finset.mem_univ i) h
  · rw [if_neg hij]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hki : k = i
    · subst hki; simp [Pi.single_eq_of_ne hij]
    · simp [Pi.single_eq_of_ne hki]

/-! ## The rank-one determinant formula -/

lemma transpose_vecMulVec (c r : Fin 3 → ℝ) :
    (Matrix.vecMulVec c r).transpose = Matrix.vecMulVec r c := by
  ext i j
  rw [Matrix.transpose_apply, Matrix.vecMulVec_apply, Matrix.vecMulVec_apply]
  ring

lemma det_one_add_vecMulVec (c r : Fin 3 → ℝ) :
    ((1 : Matrix (Fin 3) (Fin 3) ℝ) + Matrix.vecMulVec c r).det = 1 + r ⬝ᵥ c := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply, dotProduct,
    Fin.sum_univ_three]
  norm_num
  ring

/-! ## A matrix killing two independent vectors is a dyad -/

/-- A nonzero `3 × 3` matrix killing two independent vectors is a dyad. -/
lemma exists_vecMulVec (A : Matrix (Fin 3) (Fin 3) ℝ) (v w : Fin 3 → ℝ)
    (hLI : LinearIndependent ℝ ![v, w]) (hAv : A *ᵥ v = 0) (hAw : A *ᵥ w = 0) (hA : A ≠ 0) :
    ∃ c r : Fin 3 → ℝ, c ≠ 0 ∧ A = Matrix.vecMulVec c r := by
  have hfin : Module.finrank ℝ ↥(LinearMap.range (Matrix.toLin' A)) ≤ 1 := by
    have hrank := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' A)
    rw [Module.finrank_fin_fun] at hrank
    have hker : 2 ≤ Module.finrank ℝ ↥(LinearMap.ker (Matrix.toLin' A)) := by
      have hle : Submodule.span ℝ (Set.range ![v, w]) ≤ LinearMap.ker (Matrix.toLin' A) := by
        rw [Submodule.span_le]
        rintro x ⟨i, rfl⟩
        change (Matrix.toLin' A) (![v, w] i) = 0
        rw [Matrix.toLin'_apply]
        fin_cases i
        · simpa using hAv
        · simpa using hAw
      have hfr : Module.finrank ℝ ↥(Submodule.span ℝ (Set.range ![v, w])) = 2 := by
        rw [finrank_span_eq_card hLI]
        simp
      calc (2 : ℕ) = Module.finrank ℝ ↥(Submodule.span ℝ (Set.range ![v, w])) := hfr.symm
        _ ≤ Module.finrank ℝ ↥(LinearMap.ker (Matrix.toLin' A)) := Submodule.finrank_mono hle
    omega
  have hrange : LinearMap.range (Matrix.toLin' A) ≠ ⊥ := by
    intro hbot
    apply hA
    ext i j
    have hmem : A *ᵥ (Pi.single j (1 : ℝ)) ∈ LinearMap.range (Matrix.toLin' A) :=
      ⟨Pi.single j (1 : ℝ), by rw [Matrix.toLin'_apply]⟩
    rw [hbot] at hmem
    have h1 : A *ᵥ (Pi.single j (1 : ℝ)) = 0 := hmem
    have h2 := congrFun h1 i
    rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.zero_apply] at h2
    exact h2
  have hfin1 : Module.finrank ℝ ↥(LinearMap.range (Matrix.toLin' A)) = 1 := by
    have hne : Module.finrank ℝ ↥(LinearMap.range (Matrix.toLin' A)) ≠ 0 := by
      intro h0
      exact hrange (Submodule.finrank_eq_zero.mp h0)
    omega
  have hex : ∃ j : Fin 3, A.col j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hA
    ext i j
    have h1 := congrFun (h j) i
    rw [Matrix.col_apply, Pi.zero_apply] at h1
    exact h1
  obtain ⟨j, hj⟩ := hex
  set c : Fin 3 → ℝ := A *ᵥ (Pi.single j (1 : ℝ)) with hcdef
  have hcolj : A.col j = c := by rw [hcdef, Matrix.mulVec_single_one]
  have hc0 : c ≠ 0 := by rw [← hcolj]; exact hj
  have hcmem : c ∈ LinearMap.range (Matrix.toLin' A) :=
    ⟨Pi.single j (1 : ℝ), by rw [Matrix.toLin'_apply, hcdef]⟩
  have hrange_eq : LinearMap.range (Matrix.toLin' A) = Submodule.span ℝ {c} := by
    refine (Submodule.eq_of_le_of_finrank_le ?_ ?_).symm
    · rw [Submodule.span_le]
      rintro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hcmem
    · rw [finrank_span_singleton hc0]
      exact hfin
  have hcol_mem : ∀ j' : Fin 3, A.col j' ∈ Submodule.span ℝ {c} := by
    intro j'
    rw [← hrange_eq]
    exact ⟨Pi.single j' (1 : ℝ), by rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]⟩
  choose r hr using fun j' => (Submodule.mem_span_singleton).mp (hcol_mem j')
  refine ⟨c, r, hc0, ?_⟩
  ext i j'
  have h1 := congrFun (hr j') i
  rw [Matrix.col_apply] at h1
  rw [← h1, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ## A nontrivial special orthogonal `3 × 3` matrix fixes a line -/

theorem so3FixedLine_aux (S : Matrix (Fin 3) (Fin 3) ℝ) (horth : Sᵀ * S = 1)
    (hdet : S.det = 1) (hne : S ≠ 1) :
    ∃ v : Fin 3 → ℝ, v ≠ 0 ∧ ∀ w : Fin 3 → ℝ, S.mulVec w = w ↔ ∃ c : ℝ, w = c • v := by
  obtain ⟨v, hvne, hv⟩ := orth_det_one_fixedVec S horth hdet
  refine ⟨v, hvne, fun w => ⟨?_, ?_⟩⟩
  · intro hw
    by_contra hno
    have hLI : LinearIndependent ℝ ![v, w] := by
      rw [LinearIndependent.pair_iff' hvne]
      intro a ha
      exact hno ⟨a, ha.symm⟩
    set A : Matrix (Fin 3) (Fin 3) ℝ := S - 1 with hAdef
    have hAv : A *ᵥ v = 0 := by
      rw [hAdef, Matrix.sub_mulVec, hv, Matrix.one_mulVec, sub_self]
    have hAw : A *ᵥ w = 0 := by
      rw [hAdef, Matrix.sub_mulVec, hw, Matrix.one_mulVec, sub_self]
    have hA0 : A ≠ 0 := by
      intro hzero
      apply hne
      rw [hAdef] at hzero
      exact sub_eq_zero.mp hzero
    obtain ⟨c, r, hc0, hdyad⟩ := exists_vecMulVec A v w hLI hAv hAw hA0
    have hS1 : S = 1 + A := by rw [hAdef]; abel
    have hdetS : S.det = 1 + r ⬝ᵥ c := by
      rw [hS1, hdyad, det_one_add_vecMulVec]
    have hrc : r ⬝ᵥ c = 0 := by linarith [hdet, hdetS]
    have hAT : A.transpose = -(Sᵀ * A) := by
      have h1 : A.transpose = Sᵀ - 1 := by
        rw [hAdef, Matrix.transpose_sub, Matrix.transpose_one]
      rw [h1, hAdef, Matrix.mul_sub, Matrix.mul_one, horth]
      abel
    have hATdyad : A.transpose = Matrix.vecMulVec r c := by
      rw [hdyad, transpose_vecMulVec]
    have hstar : (c ⬝ᵥ c) • r = -(r ⬝ᵥ c) • (Sᵀ *ᵥ c) := by
      have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M *ᵥ c) hAT
      have h1 : A.transpose *ᵥ c = (c ⬝ᵥ c) • r := by
        rw [hATdyad, Matrix.vecMulVec_mulVec, op_smul_eq_smul]
      have h2 : (-(Sᵀ * A)) *ᵥ c = -(r ⬝ᵥ c) • (Sᵀ *ᵥ c) := by
        rw [Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, hdyad, Matrix.vecMulVec_mulVec,
          op_smul_eq_smul, Matrix.mulVec_smul, ← neg_smul]
      rw [h1, h2] at h
      exact h
    have hcc : c ⬝ᵥ c ≠ 0 := dotProduct_self_ne_zero hc0
    have hzero : (c ⬝ᵥ c) • r = 0 := by
      rw [hstar, hrc]
      simp
    have hr0 : r = 0 := by
      rcases (smul_eq_zero.mp hzero) with h | h
      · exact absurd h hcc
      · exact h
    have hAz : A = 0 := by
      rw [hdyad, hr0]
      ext i j
      simp [Matrix.vecMulVec_apply]
    exact hA0 hAz
  · rintro ⟨c, rfl⟩
    rw [Matrix.mulVec_smul, hv]

/-! ## The block form of `emat g` at a fixed base point -/

theorem ematZeroBlock_aux (g : PO 3 1) (hg : g • (0 : E 3) = 0) :
    ∃ S : Matrix (Fin 3) (Fin 3) ℝ,
      (Work.Mostow.emat g = Matrix.fromBlocks S 0 0 1) ∧
      Sᵀ * S = 1 ∧
      (∀ u : E 3, S.mulVec (fun j => u j) = fun i => (g • u) i) := by
  obtain ⟨hsheet, hisom, -⟩ := Work.Mostow.ematSpec g
  have hmink_single : ∀ x : Fin 3 ⊕ Fin 1 → ℝ,
      Work.Mostow.mink x (Pi.single (Sum.inr 0) (1 : ℝ)) = - x (Sum.inr 0) := by
    intro x
    simp [Work.Mostow.mink, dotProduct]
  have hcol : Work.Mostow.emat g *ᵥ Pi.single (Sum.inr 0) (1 : ℝ)
      = Pi.single (Sum.inr 0) (1 : ℝ) := by
    have h := hsheet 0
    rw [hg] at h
    simpa [Hyper.hlift_zero, Hyper.etime] using h
  have hcol' : (Work.Mostow.emat g).col (Sum.inr 0) = Pi.single (Sum.inr 0) (1 : ℝ) := by
    rw [← Matrix.mulVec_single_one (Work.Mostow.emat g) (Sum.inr 0)]
    exact hcol
  have htime : ∀ x : Fin 3 ⊕ Fin 1 → ℝ,
      (Work.Mostow.emat g *ᵥ x) (Sum.inr 0) = x (Sum.inr 0) := by
    intro x
    have h := hisom x (Pi.single (Sum.inr 0) (1 : ℝ))
    rw [hcol, hmink_single, hmink_single] at h
    linarith
  have h1 : ∀ i : Fin 3, (Work.Mostow.emat g) (Sum.inl i) (Sum.inr 0) = 0 := by
    intro i
    have h := congrFun hcol' (Sum.inl i)
    rw [Matrix.col_apply] at h
    simpa using h
  have h3 : ∀ j : Fin 3, (Work.Mostow.emat g) (Sum.inr 0) (Sum.inl j) = 0 := by
    intro j
    have h := htime (Pi.single (Sum.inl j) (1 : ℝ))
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at h
    simpa using h
  have h4 : (Work.Mostow.emat g) (Sum.inr 0) (Sum.inr 0) = 1 := by
    have h := htime (Pi.single (Sum.inr 0) (1 : ℝ))
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at h
    simpa using h
  set S : Matrix (Fin 3) (Fin 3) ℝ := fun i j => (Work.Mostow.emat g) (Sum.inl i) (Sum.inl j)
    with hSdef
  have hblock : Work.Mostow.emat g = Matrix.fromBlocks S 0 0 1 := by
    ext a b
    rcases a with i | i <;> rcases b with j | j
    · rw [Matrix.fromBlocks_apply₁₁]
    · obtain rfl : j = 0 := Subsingleton.elim j 0
      rw [Matrix.fromBlocks_apply₁₂, h1 i]
      simp
    · obtain rfl : i = 0 := Subsingleton.elim i 0
      rw [Matrix.fromBlocks_apply₂₁, h3 j]
      simp
    · obtain rfl : i = 0 := Subsingleton.elim i 0
      obtain rfl : j = 0 := Subsingleton.elim j 0
      rw [Matrix.fromBlocks_apply₂₂, h4]
      simp
  have hmink_wv : ∀ a b : Fin 3 → ℝ,
      Work.Mostow.mink (Sum.elim a (fun _ => 0)) (Sum.elim b (fun _ => 0)) = a ⬝ᵥ b := by
    intro a b
    simp [Work.Mostow.mink, dotProduct]
  -- the action of `S` on the chart
  have hac : ∀ u : E 3, S.mulVec (fun j => u j) = fun i => (g • u) i := by
    intro u
    funext i
    have ha1 : (Work.Mostow.emat g *ᵥ hlift u) (Sum.inl i)
        = ∑ j : Fin 3, (Work.Mostow.emat g) (Sum.inl i) (Sum.inl j) * u j := by
      calc (Work.Mostow.emat g *ᵥ hlift u) (Sum.inl i)
          = ∑ z : Fin 3 ⊕ Fin 1, (Work.Mostow.emat g) (Sum.inl i) z * hlift u z := by
            simp [Matrix.mulVec, dotProduct]
        _ = (∑ z : Fin 3, (Work.Mostow.emat g) (Sum.inl i) (Sum.inl z)
                * hlift u (Sum.inl z))
              + ∑ z : Fin 1, (Work.Mostow.emat g) (Sum.inl i) (Sum.inr z)
                * hlift u (Sum.inr z) := by
            rw [Fintype.sum_sum_type]
        _ = (∑ z : Fin 3, (Work.Mostow.emat g) (Sum.inl i) (Sum.inl z) * u z)
              + (Work.Mostow.emat g) (Sum.inl i) (Sum.inr 0) * tpart u := by
            rw [Fin.sum_univ_one]
            simp [hlift]
        _ = ∑ z : Fin 3, (Work.Mostow.emat g) (Sum.inl i) (Sum.inl z) * u z := by
            rw [h1 i, zero_mul, add_zero]
    have ha2 : (S.mulVec (fun j => u j)) i
        = ∑ j : Fin 3, (Work.Mostow.emat g) (Sum.inl i) (Sum.inl j) * u j := by
      calc (S.mulVec (fun j => u j)) i
          = ∑ j : Fin 3, S i j * u j := by simp [Matrix.mulVec, dotProduct]
        _ = ∑ j : Fin 3, (Work.Mostow.emat g) (Sum.inl i) (Sum.inl j) * u j :=
            Finset.sum_congr rfl fun j _ => by rw [hSdef]
    have h := congrFun (hsheet u) (Sum.inl i)
    rw [ha1] at h
    rw [show hlift (g • u) (Sum.inl i) = (g • u) i from rfl] at h
    rw [← ha2] at h
    exact h
  -- `g` preserves the hyperbolic inner product
  have htpart : ∀ u : E 3, tpart (g • u) = tpart u := by
    intro u
    have h := htime (hlift u)
    rw [hsheet u] at h
    exact h
  have hinner : ∀ u v : E 3, inner ℝ (g • u) (g • v) = inner ℝ u v := by
    intro u v
    have h := hisom (hlift u) (hlift v)
    rw [hsheet u, hsheet v, mink_hlift_hlift, mink_hlift_hlift] at h
    rw [htpart u, htpart v] at h
    linarith
  have horth : Sᵀ * S = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have huu : ∀ k, (g • (EuclideanSpace.single i (1 : ℝ) : E 3)) k = S k i := by
      intro k
      have h1c := congrFun (hac (EuclideanSpace.single i (1 : ℝ) : E 3)) k
      rw [← h1c]
      have h2 : (fun j => (EuclideanSpace.single i (1 : ℝ) : E 3) j) = Pi.single i (1 : ℝ) :=
        funext fun j => rfl
      rw [h2, Matrix.mulVec_single_one, Matrix.col_apply]
    have hvv : ∀ k, (g • (EuclideanSpace.single j (1 : ℝ) : E 3)) k = S k j := by
      intro k
      have h1c := congrFun (hac (EuclideanSpace.single j (1 : ℝ) : E 3)) k
      rw [← h1c]
      have h2 : (fun j' => (EuclideanSpace.single j (1 : ℝ) : E 3) j') = Pi.single j (1 : ℝ) :=
        funext fun j' => rfl
      rw [h2, Matrix.mulVec_single_one, Matrix.col_apply]
    have h := hinner (EuclideanSpace.single i (1 : ℝ) : E 3)
      (EuclideanSpace.single j (1 : ℝ) : E 3)
    rw [Hyper.inner_eq_sum, Hyper.inner_eq_sum] at h
    have hL : (∑ k, (g • (EuclideanSpace.single i (1 : ℝ) : E 3)) k
          * (g • (EuclideanSpace.single j (1 : ℝ) : E 3)) k) = ∑ k, S k i * S k j :=
      Finset.sum_congr rfl fun k _ => by rw [huu k, hvv k]
    have hR : (∑ k, (EuclideanSpace.single i (1 : ℝ) : E 3) k
          * (EuclideanSpace.single j (1 : ℝ) : E 3) k) = (if i = j then (1 : ℝ) else 0) := by
      have h' : (Pi.single i (1 : ℝ) : Fin 3 → ℝ) ⬝ᵥ (Pi.single j (1 : ℝ))
          = (if i = j then (1 : ℝ) else 0) := dot_single i j
      rw [dotProduct] at h'
      exact h'
    rw [hL, hR] at h
    rw [← h]
    exact Finset.sum_congr rfl fun k _ => by
      have h2 : Sᵀ i k = S k i := Matrix.transpose_apply S i k
      rw [h2]
  exact ⟨S, hblock, horth, hac⟩

/-! ## The main theorem -/

theorem axis_fixeset (hA : Submission.Mostow.POActionProp 3) (hI : Submission.Mostow.HypIsometryProp 3)
    (f : LeanEval.Geometry.MostowRigidity.PO 3 1) (hf : f ≠ 1) (hfin : IsOfFinOrder f)
    (hor : Work.Mostow.IsOriented f) :
    ∃ a b : Submission.Mostow.E 3, a ∈ Submission.Mostow.Sph 3 ∧ b ∈ Submission.Mostow.Sph 3 ∧ a ≠ b ∧
      ∀ u : Submission.Mostow.E 3, f • u = u ↔ u ∈ Work.Mostow.geodSet a b := by
  have hAb := POBasic.ofProp hA
  have hIb := HypIsoData.ofProp hI
  obtain ⟨N, hN, hfN⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
  have hpow : ∀ m : ℕ, f ^ m = f ^ (m % N) := by
    intro m
    conv_lhs => rw [← Nat.mod_add_div m N]
    rw [pow_add, pow_mul, hfN, one_pow, mul_one]
  have hbdd : ∃ R : ℝ, ∀ m : ℕ, hdist (0 : E 3) ((f ^ m) • (0 : E 3)) ≤ R := by
    refine ⟨∑ i ∈ Finset.range N, hdist (0 : E 3) ((f ^ i) • (0 : E 3)), fun m => ?_⟩
    rw [hpow m]
    exact Finset.single_le_sum (fun i _ => hIb.nonneg 0 ((f ^ i) • (0 : E 3)))
      (Finset.mem_range.mpr (Nat.mod_lt m hN))
  obtain ⟨p, hp⟩ := boundedOrbitFixed 3 (by norm_num) hA hI f 0 hbdd
  set β : PO 3 1 := ((Work.Mostow.boost p : O1 3) : PO 3 1) with hβdef
  have hβ0 : β • (0 : E 3) = p := Work.Mostow.boost_smul_zero hA p
  set g : PO 3 1 := β⁻¹ * f * β with hgdef
  have hg0 : g • (0 : E 3) = 0 := by
    show (β⁻¹ * f * β) • (0 : E 3) = 0
    rw [hAb.mul_smul, hAb.mul_smul, hβ0, hp, ← hβ0, ← hAb.mul_smul, inv_mul_cancel,
      hAb.one_smul]
  obtain ⟨hmatmul, hmatone, hmatinv, hmatdet, hmat_or⟩ := Work.Mostow.gapA.ematMulDet
  have hdetf : 0 < (Work.Mostow.emat f).det := (hmat_or f).mp hor
  have hdet1 : (Work.Mostow.emat g).det = (Work.Mostow.emat f).det := by
    have h1 : Work.Mostow.emat g
        = Work.Mostow.emat β⁻¹ * Work.Mostow.emat f * Work.Mostow.emat β := by
      rw [hgdef, hmatmul, hmatmul]
    rw [h1, Matrix.det_mul, Matrix.det_mul]
    have hb : (Work.Mostow.emat β⁻¹).det * (Work.Mostow.emat β).det = 1 := by
      rw [← Matrix.det_mul, ← hmatmul, inv_mul_cancel, hmatone, Matrix.det_one]
    linear_combination (Work.Mostow.emat f).det * hb
  obtain ⟨S, hblock, horth, hact⟩ := ematZeroBlock_aux g hg0
  have hSdet : S.det = (Work.Mostow.emat f).det := by
    have h1 : S.det = (Work.Mostow.emat g).det := by
      rw [hblock, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]
    rw [h1, hdet1]
  have hSdet1 : S.det = 1 := by
    have hsq : S.det * S.det = 1 := by
      have h := congrArg Matrix.det horth
      rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
      exact h
    have hpos : 0 < S.det := by rw [hSdet]; exact hdetf
    nlinarith [hsq, hpos]
  have hSne : S ≠ 1 := by
    intro hS
    apply hf
    have hgid : g = 1 := hAb.faithful g (fun u => by
      have h := hact u
      rw [hS, Matrix.one_mulVec] at h
      have h3 : WithLp.toLp 2 (fun j => u j) = WithLp.toLp 2 (fun i => (g • u) i) :=
        congrArg (WithLp.toLp 2) h
      simpa using h3.symm)
    have h2 : β⁻¹ * f * β = 1 := by rw [← hgdef]; exact hgid
    have h3 : f = β * (β⁻¹ * f * β) * β⁻¹ := by group
    rw [h2, mul_one, mul_inv_cancel] at h3
    exact h3
  obtain ⟨v, hvne, hvfix⟩ := so3FixedLine_aux S horth hSdet1 hSne
  set a₀ : E 3 := WithLp.toLp 2 v with ha₀def
  have ha₀ne : a₀ ≠ 0 := by
    intro h
    apply hvne
    have h3 : WithLp.ofLp a₀ = WithLp.ofLp (0 : E 3) := congrArg WithLp.ofLp h
    simpa [ha₀def] using h3
  set â : E 3 := (‖a₀‖)⁻¹ • a₀ with hâdef
  have hâ_sph : â ∈ Sph 3 := by
    rw [mem_Sph_iff, hâdef, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr ha₀ne)]
  have hnegâ : -â ∈ Sph 3 := by
    rw [mem_Sph_iff, norm_neg]; exact (mem_Sph_iff â).mp hâ_sph
  have ha₀â : a₀ = ‖a₀‖ • â := by
    rw [hâdef, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr ha₀ne), one_smul]
  have hline : ∀ u : E 3, (∃ c : ℝ, (fun j => u j) = c • v) ↔ ∃ c : ℝ, u = c • â := by
    intro u
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c * ‖a₀‖, ?_⟩
      have h2 : u = c • a₀ := by
        rw [show u = WithLp.toLp 2 (fun j => u j) from rfl, hc]
        rfl
      rw [h2]
      conv_lhs => rw [ha₀â]
      rw [smul_smul]
    · rintro ⟨c, hc⟩
      have hâv : (fun j => â j) = ‖a₀‖⁻¹ • v := by
        rw [hâdef]
        funext j
        rw [smul_coe, ha₀def]
        rfl
      refine ⟨c * ‖a₀‖⁻¹, ?_⟩
      rw [hc, show (fun j => (c • â) j) = c • (fun j => â j) from rfl, hâv, smul_smul]
  have hfixg : ∀ u : E 3, g • u = u ↔ u ∈ geodSet â (-â) := by
    intro u
    rw [geodSetAxis_aux â hâ_sph u]
    constructor
    · intro hgu
      have h1 : S.mulVec (fun j => u j) = (fun j => u j) := by
        have h2 := hact u
        rw [hgu] at h2
        exact h2
      exact (hline u).mp ((hvfix (fun j => u j)).mp h1)
    · rintro hlin
      have h1 : S.mulVec (fun j => u j) = (fun j => u j) :=
        (hvfix (fun j => u j)).mpr ((hline u).mpr hlin)
      have h2 := hact u
      rw [h1] at h2
      have h3 : WithLp.toLp 2 (fun j => u j) = WithLp.toLp 2 (fun i => (g • u) i) :=
        congrArg (WithLp.toLp 2) h2
      simpa using h3.symm
  have hinj : ∀ x y : E 3, β⁻¹ • x = β⁻¹ • y → x = y := by
    intro x y hxy
    have h4 : β • (β⁻¹ • x) = β • (β⁻¹ • y) := by rw [hxy]
    rwa [← hAb.mul_smul β β⁻¹ x, ← hAb.mul_smul β β⁻¹ y, mul_inv_cancel, hAb.one_smul,
      hAb.one_smul] at h4
  have hkey : ∀ u : E 3, (β⁻¹ * f * β) • (β⁻¹ • u) = β⁻¹ • (f • u) := by
    intro u
    rw [hAb.mul_smul, hAb.mul_smul, ← hAb.mul_smul β β⁻¹ u, mul_inv_cancel, hAb.one_smul]
  have hfixconv : ∀ u : E 3, g • (β⁻¹ • u) = β⁻¹ • u ↔ f • u = u := by
    intro u
    constructor
    · intro h
      have h1 : β⁻¹ • (f • u) = β⁻¹ • u := by
        rw [← hkey u]
        exact h
      exact hinj (f • u) u h1
    · intro h
      show (β⁻¹ * f * β) • (β⁻¹ • u) = β⁻¹ • u
      rw [hkey u, h]
  have hgeod := (geodEquiv 3 (by norm_num) hA hI â (-â) hâ_sph hnegâ β).2
  have hfixf : ∀ u : E 3, f • u = u ↔ u ∈ geodSet (bd β â) (bd β (-â)) := by
    intro u
    rw [← hfixconv u, hfixg (β⁻¹ • u), hgeod (β⁻¹ • u)]
    rw [← hAb.mul_smul β β⁻¹ u, mul_inv_cancel, hAb.one_smul]
  have hbdeq : bd β â ≠ bd β (-â) := by
    intro h
    have h1 : bd β⁻¹ (bd β â) = â := by
      rw [← hAb.bd_mul β⁻¹ β â hâ_sph, inv_mul_cancel, hAb.bd_one â hâ_sph]
    have h2 : bd β⁻¹ (bd β (-â)) = -â := by
      rw [← hAb.bd_mul β⁻¹ β (-â) hnegâ, inv_mul_cancel, hAb.bd_one (-â) hnegâ]
    rw [h] at h1
    rw [h2] at h1
    have h3 : â + â = 0 := by
      nth_rewrite 2 [← h1]
      exact add_neg_cancel â
    have h3' : (2 : ℝ) • â = 0 := by rw [two_smul]; exact h3
    have h4 : â = 0 := by
      rcases (smul_eq_zero.mp h3') with h5 | h5
      · exact absurd h5 (by norm_num)
      · exact h5
    have h5 : ‖â‖ = 1 := (mem_Sph_iff â).mp hâ_sph
    rw [h4, norm_zero] at h5
    exact absurd h5 (by norm_num)
  exact ⟨bd β â, bd β (-â), hAb.bd_mem β â hâ_sph, hAb.bd_mem β (-â) hnegâ, hbdeq, hfixf⟩

end

end Work.Mostow.gapA
