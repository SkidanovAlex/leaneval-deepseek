import Mathlib
import Submission.LocalCurve
import Submission.Work.Drive.meridianFibreDefs

/-!
# The analytic local-curve theorem for the collinearity zero set

The verbatim analytic (`C^ω`) analogue of `Submission/LocalCurve.lean`'s
`smooth_local_curve_of_general_position` / `LocalSmoothCurveTheorem`: near every general-position
collinear off-diagonal triple the off-diagonal zero set of the collinearity map is an injectively
parametrised *analytic* curve through the triple.

The proof is the copy of the `C¹` proof with the regularity `1` replaced by `⊤` (the analytic
class `ω`): the only change of substance is that the implicit function theorem is invoked with
`n = ⊤` (`Work.Drive.implicitFunction_graph_omega` below), which Mathlib's
`ContDiffAt.implicitFunction` affords.  The auxiliary machinery (`pairReduced`,
`pairReduced_fderiv_range_top`, the splits `splitAB`/`splitAM`/`splitBM`, `split_col_helper`,
`axis_path_col`, `linearIndependent_pair_swap_iff`) is imported from `Submission/LocalCurve.lean`
and reused unchanged.
-/

open LeanEval.KnotTheory.Quadrisecant
open scoped Topology Matrix
open Filter
open Commons.Analysis.Calculus.FDeriv
open Commons.LinearAlgebra.LinearIndependent
set_option maxHeartbeats 800000

noncomputable section

namespace Work.Drive

/-- The implicit function theorem in graph form, analytic regularity: if `f : ℝ × E₂ → F` is
analytic at `u`, vanishes at `u`, and its partial derivative with respect to the second
coordinate at `u` is invertible, then locally the zero set of `f` is the graph of an analytic
function `ψ : ℝ → E₂` over the first coordinate, with `ψ u.1 = u.2`. -/
theorem implicitFunction_graph_omega
    {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [CompleteSpace E₂]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {u : ℝ × E₂} {f : ℝ × E₂ → F}
    (cdf : ContDiffAt ℝ ⊤ f u) (h0 : f u = 0)
    (if₂ : (fderiv ℝ f u ∘L .inr ℝ ℝ E₂).IsInvertible) :
    ∃ ψ : ℝ → E₂,
      ψ u.1 = u.2 ∧
      (∃ V : Set ℝ, V ∈ 𝓝 u.1 ∧ ContDiffOn ℝ ⊤ ψ V ∧ (∀ x ∈ V, f (x, ψ x) = 0)) ∧
      (∀ᶠ v in 𝓝 u, f v = 0 → ψ v.1 = v.2) := by
  let ψ : ℝ → E₂ := cdf.implicitFunction (by norm_num) if₂
  refine ⟨ψ, ?_, ?_, ?_⟩
  · exact cdf.implicitFunction_apply_self (by norm_num) if₂
  · have hca : ContDiffAt ℝ ⊤ ψ u.1 := by
      simpa [ψ] using (cdf.contDiffAt_implicitFunction (by norm_num) if₂)
    rcases hca.contDiffOn le_rfl (by intro h; exact absurd h (by norm_num)) with ⟨W, hW, hcW⟩
    have hz : ∀ᶠ x in 𝓝 u.1, f (x, ψ x) = 0 := by
      filter_upwards [cdf.eventually_apply_implicitFunction (by norm_num) if₂] with x hx
      simpa [ψ, h0] using hx
    rcases eventually_iff_exists_mem.mp hz with ⟨Z, hZ, hZ'⟩
    refine ⟨W ∩ Z, Filter.inter_mem hW hZ, ?_, ?_⟩
    · exact hcW.mono (by intro x hx; exact hx.1)
    · intro x hx
      exact hZ' x hx.2
  · filter_upwards [cdf.eventually_apply_eq_iff_implicitFunction (by norm_num) if₂] with v hv
    intro hfv
    exact (hv.mp (by simpa [h0] using hfv))

theorem analyticTrisecantLocalCurve_of_splitData
    {r : ℝ → Space} (h : IsSmoothKnot r)
    (p : RealParamTriple)
    (hColl : collinearityMap r p = 0) (hOff : p ∈ RealOffDiagonalTriples r)
    (A : ℝ × (ℝ × ℝ) → RealParamTriple) (B : RealParamTriple → ℝ × (ℝ × ℝ))
    (hAcd : ContDiff ℝ ⊤ A) (hBcont : Continuous B)
    (hAB : ∀ z, B (A z) = z) (hBA : ∀ q, A (B q) = q)
    (u : ℝ × (ℝ × ℝ)) (hu : A u = p)
    (red : RealParamTriple → ℝ × ℝ)
    (hCdA : ContDiff ℝ ⊤ (red ∘ A))
    (hred0 : red p = (0, 0))
    (hred_of_collinear : ∀ q : RealParamTriple, collinearityMap r q = 0 → red q = (0, 0))
    (if₂ : ((fderiv ℝ (red ∘ A) u) ∘L .inr ℝ ℝ (ℝ × ℝ)).IsInvertible)
    (hident : ∃ U : Set RealParamTriple, IsOpen U ∧ p ∈ U ∧
      ∀ q ∈ U, red q = (0, 0) → collinearityMap r q = 0) :
    AnalyticTrisecantLocalCurve r p := by
  rcases hident with ⟨Uid, hUido, hUidp, hUid⟩
  -- ψ from the product-domain implicit function theorem
  rcases implicitFunction_graph_omega
    (u := u) (f := red ∘ A)
    (cdf := ContDiff.contDiffAt hCdA)
    (h0 := by
      change red (A u) = (0, 0)
      rw [hu]
      exact hred0)
    (if₂ := if₂) with ⟨ψ, hψu, hψV, hcover⟩
  rcases hψV with ⟨V, hVV, hψcd, hψval⟩
  -- the covering neighbourhood W, in open form
  have hWex : ∃ W : Set (ℝ × (ℝ × ℝ)), IsOpen W ∧ u ∈ W ∧
      ∀ v ∈ W, (red ∘ A) v = (0, 0) → ψ v.1 = v.2 := by
    rcases hcover.exists_mem with ⟨W₀, hW₀u, hW₀⟩
    rcases mem_nhds_iff.mp hW₀u with ⟨W, hWsub, hWopen, hWu⟩
    refine ⟨W, hWopen, hWu, ?_⟩
    intro v hv
    exact hW₀ v (hWsub hv)
  rcases hWex with ⟨W, hWopen, hWu, hW⟩
  -- ψ is C¹ at u.1 (hence continuous), since V is a neighbourhood of u.1
  have hψcdAt : ContDiffAt ℝ ⊤ ψ u.1 := ContDiffOn.contDiffAt hψcd hVV
  have hψcontAt : ContinuousAt ψ u.1 := hψcdAt.continuousAt
  have hpathcont : ContinuousAt (fun x : ℝ => (x, ψ x)) u.1 := by
    have hfw : ContinuousWithinAt (fun x : ℝ => x) Set.univ u.1 :=
      (continuousAt_id (x := u.1)).continuousWithinAt
    have hgw : ContinuousWithinAt ψ Set.univ u.1 :=
      (continuousWithinAt_univ ψ u.1).mpr hψcontAt
    exact (continuousWithinAt_univ (fun x : ℝ => (x, ψ x)) u.1).mp
      (ContinuousWithinAt.prodMk hfw hgw)
  -- the open set of good curve values
  let Uoff : Set RealParamTriple := RealOffDiagonalTriples r
  have hUoffo : IsOpen Uoff := isOpen_RealOffDiagonalTriples h
  let G : Set RealParamTriple := Uid ∩ Uoff
  have hGo : IsOpen G := hUido.inter hUoffo
  have hGp : p ∈ G := ⟨hUidp, hOff⟩
  -- small intervals around u.1 on which (x,ψx) ∈ W, A(x,ψx) ∈ G, and x ∈ V
  have hS1 : ∃ a b : ℝ, a < u.1 ∧ u.1 < b ∧ ∀ x ∈ Set.Ioo a b, (x, ψ x) ∈ W := by
    rcases exists_Ioo_subset_of_mem_nhds (hpathcont.preimage_mem_nhds
        (hWopen.mem_nhds (by simpa [hψu] using hWu)))
      with ⟨a, b, ha, hb, hab⟩
    refine ⟨a, b, ha, hb, ?_⟩
    intro x hx
    exact hab hx
  rcases hS1 with ⟨a1, b1, ha1, hb1, hS1⟩
  have hS2 : ∃ a b : ℝ, a < u.1 ∧ u.1 < b ∧
      ∀ x ∈ Set.Ioo a b, A (x, ψ x) ∈ G := by
    have hAcontAt : ContinuousAt (fun x : ℝ => A (x, ψ x)) u.1 :=
      (hAcd.continuous.continuousAt.comp hpathcont)
    rcases exists_Ioo_subset_of_mem_nhds (hAcontAt.preimage_mem_nhds
        (hGo.mem_nhds (by simpa [hψu, hu] using hGp)))
      with ⟨a, b, ha, hb, hab⟩
    refine ⟨a, b, ha, hb, ?_⟩
    intro x hx
    exact hab hx
  rcases hS2 with ⟨a2, b2, ha2, hb2, hS2⟩
  have hS0 : ∃ a b : ℝ, a < u.1 ∧ u.1 < b ∧ Set.Ioo a b ⊆ V := exists_Ioo_subset_of_mem_nhds hVV
  rcases hS0 with ⟨a0, b0, ha0, hb0, hS0⟩
  -- pick an interval inside all three
  let a : ℝ := max a0 (max a1 a2)
  let b : ℝ := min b0 (min b1 b2)
  have ha : a < u.1 := by
    dsimp [a]
    exact max_lt ha0 (max_lt ha1 ha2)
  have hb : u.1 < b := by
    dsimp [b]
    exact lt_min hb0 (lt_min hb1 hb2)
  have hIab : ∀ x ∈ Set.Ioo a b,
      x ∈ V ∧ (x, ψ x) ∈ W ∧ A (x, ψ x) ∈ G := by
    intro x hx
    have hxa0 : x ∈ Set.Ioo a0 b0 := by
      constructor
      · exact lt_of_le_of_lt (le_max_left a0 (max a1 a2)) hx.1
      · exact lt_of_lt_of_le hx.2 (min_le_left b0 (min b1 b2))
    have hxa1 : x ∈ Set.Ioo a1 b1 := by
      constructor
      · exact lt_of_le_of_lt (le_trans (le_max_left a1 a2) (le_max_right a0 (max a1 a2))) hx.1
      · exact lt_of_lt_of_le hx.2 (le_trans (min_le_right b0 (min b1 b2)) (min_le_left b1 b2))
    have hxa2 : x ∈ Set.Ioo a2 b2 := by
      constructor
      · exact lt_of_le_of_lt (le_trans (le_max_right a1 a2) (le_max_right a0 (max a1 a2))) hx.1
      · exact lt_of_lt_of_le hx.2 (le_trans (min_le_right b0 (min b1 b2)) (min_le_right b1 b2))
    exact ⟨hS0 hxa0, hS1 x hxa1, hS2 x hxa2⟩

  -- final parameters of the curve
  let lo : ℝ := a - u.1
  let hi : ℝ := b - u.1
  have hlo : lo < 0 := by dsimp [lo]; linarith
  have hhi : 0 < hi := by dsimp [hi]; linarith
  let γ0 : ℝ → RealParamTriple := fun x => A (x, ψ x)
  let γ : ℝ → RealParamTriple := fun t => γ0 (u.1 + t)
  -- the final neighbourhood
  let U : Set RealParamTriple :=
    {q | (B q).1 ∈ Set.Ioo a b} ∩ (G ∩ (B ⁻¹' W))
  have hUo : IsOpen U := by
    dsimp [U]
    have hBfst : Continuous (fun q : RealParamTriple => (B q).1) := continuous_fst.comp hBcont
    exact (isOpen_Ioo.preimage hBfst).inter (hGo.inter (hWopen.preimage hBcont))
  have hUp : p ∈ U := by
    dsimp [U]
    constructor
    · have hBp : (B p).1 = u.1 := by
        calc (B p).1 = (B (A u)).1 := by rw [← hu]
          _ = u.1 := by simp [hAB]
      change (B p).1 ∈ Set.Ioo a b
      rw [hBp]
      exact ⟨ha, hb⟩
    · exact ⟨⟨hUidp, hOff⟩, by simpa [hAB, ← hu] using hWu⟩
  -- curve values: membership, collinearity, off-diagonal
  have hγmem : ∀ t ∈ Set.Ioo lo hi,
      γ t ∈ U ∧ collinearityMap r (γ t) = 0 ∧ γ t ∈ RealOffDiagonalTriples r := by
    intro t ht
    let x : ℝ := u.1 + t
    have hxI : x ∈ Set.Ioo a b := by
      dsimp [x]
      constructor <;> linarith [ht.1, ht.2]
    have hxV : x ∈ V := (hIab x hxI).1
    have hxW : (x, ψ x) ∈ W := (hIab x hxI).2.1
    have hxG : A (x, ψ x) ∈ G := (hIab x hxI).2.2
    have hredγ : red (γ t) = (0, 0) := by
      dsimp [γ, γ0, x]
      exact hψval x hxV
    have hcollγ : collinearityMap r (γ t) = 0 := by
      exact hUid (γ t) hxG.1 hredγ
    have hUmem : γ t ∈ U := by
      change (B (γ t)).1 ∈ Set.Ioo a b ∧ γ t ∈ G ∧ B (γ t) ∈ W
      constructor
      · have hBγ : B (γ t) = (u.1 + t, ψ (u.1 + t)) := by
          dsimp [γ, γ0]
          exact hAB (u.1 + t, ψ (u.1 + t))
        rw [hBγ]
        simpa [x] using hxI
      · constructor
        · simpa [γ, γ0, x] using hxG
        · have hBγ : B (γ t) = (u.1 + t, ψ (u.1 + t)) := by
            dsimp [γ, γ0]
            exact hAB (u.1 + t, ψ (u.1 + t))
          rw [hBγ]
          simpa [x] using hxW
    exact ⟨hUmem, hcollγ, hUmem.2.1.2⟩
  -- covering
  have hcover2 : ∀ q ∈ U, collinearityMap r q = 0 → q ∈ RealOffDiagonalTriples r →
      ∃ t ∈ Set.Ioo lo hi, γ t = q := by
    intro q hqU hcl hqoff
    have hredq : red q = (0, 0) := hred_of_collinear q hcl
    let v : ℝ × (ℝ × ℝ) := B q
    have hvfR : (red ∘ A) v = (0, 0) := by
      dsimp [v]
      rw [hBA]
      exact hredq
    have hvW : v ∈ W := hqU.2.2
    have hψv : ψ v.1 = v.2 := hW v hvW hvfR
    have hvI : v.1 ∈ Set.Ioo a b := hqU.1
    let t : ℝ := v.1 - u.1
    have ht : t ∈ Set.Ioo lo hi := by
      dsimp [t, lo, hi]
      constructor <;> linarith [hvI.1, hvI.2]
    refine ⟨t, ht, ?_⟩
    dsimp [γ, γ0, t, v]
    have hsum : u.1 + ((B q).1 - u.1) = (B q).1 := by ring
    rw [hsum, hψv]
    exact hBA q
  refine ⟨hColl, hOff, U, hUo, hUp, lo, hi, hlo, hhi, γ, ?_, ?_, ?_, ?_, hcover2, ?_⟩
  · -- ContDiffOn ℝ ⊤ γ (Ioo lo hi)
    have hγcd : ContDiffOn ℝ ⊤ γ (Set.Ioo lo hi) := by
      have hshift : ContDiffOn ℝ ⊤ (fun t : ℝ => u.1 + t) (Set.Ioo lo hi) := by
        fun_prop
      have hψon : ContDiffOn ℝ ⊤ ψ (Set.Ioo a b) := by
        refine hψcd.mono ?_
        intro x hx
        exact hS0 ⟨lt_of_le_of_lt (le_max_left a0 (max a1 a2)) hx.1,
          lt_of_lt_of_le hx.2 (min_le_left b0 (min b1 b2))⟩
      have hψsh : ContDiffOn ℝ ⊤ (fun t : ℝ => ψ (u.1 + t)) (Set.Ioo lo hi) :=
        ContDiffOn.comp hψon hshift (by
          intro t ht
          constructor <;> linarith [ht.1, ht.2])
      have hpair : ContDiffOn ℝ ⊤ (fun t : ℝ => (u.1 + t, ψ (u.1 + t))) (Set.Ioo lo hi) :=
        hshift.prodMk hψsh
      have hA1 : ContDiff ℝ ⊤ A := hAcd
      have hcomp2 : ContDiffOn ℝ ⊤ (fun t : ℝ => A (u.1 + t, ψ (u.1 + t))) (Set.Ioo lo hi) := by
        change ContDiffOn ℝ ⊤ (A ∘ (fun t : ℝ => (u.1 + t, ψ (u.1 + t)))) (Set.Ioo lo hi)
        exact ContDiff.comp_contDiffOn (g := A) (n := ⊤) hA1 hpair
      exact hcomp2
    exact hγcd
  · -- injective on (lo,hi)
    intro t1 ht1 t2 ht2 hEq
    have hBγ1 : B (γ t1) = (u.1 + t1, ψ (u.1 + t1)) := by
      dsimp [γ, γ0]
      exact hAB (u.1 + t1, ψ (u.1 + t1))
    have hBγ2 : B (γ t2) = (u.1 + t2, ψ (u.1 + t2)) := by
      dsimp [γ, γ0]
      exact hAB (u.1 + t2, ψ (u.1 + t2))
    have hEq' : (u.1 + t1, ψ (u.1 + t1)) = (u.1 + t2, ψ (u.1 + t2)) := by
      simpa [hBγ1, hBγ2] using congrArg B hEq
    have hfirst : u.1 + t1 = u.1 + t2 := congrArg Prod.fst hEq'
    linarith
  · -- γ 0 = p
    dsimp [γ, γ0]
    rw [add_zero]
    rw [hψu]
    rw [hu]
  · -- values of γ in U, collinear and off-diagonal
    intro t ht
    exact hγmem t ht
  · -- the continuous local inverse of the parametrisation
    refine ⟨fun q : RealParamTriple => (B q).1 - u.1, ?_, ?_⟩
    · exact ((continuous_fst.comp hBcont).sub continuous_const).continuousOn
    · intro t ht
      have hBγ : B (γ t) = (u.1 + t, ψ (u.1 + t)) := by
        dsimp [γ, γ0]
        exact hAB (u.1 + t, ψ (u.1 + t))
      dsimp only
      rw [hBγ]
      simp

theorem analyticLocalSmoothCurve_AB {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ)
    (hΦ : collinearityValue r a b m = 0)
    (hZ : r a - r b ≠ 0) (hW0 : r a - r m ≠ 0) (hmb : r m - r b ≠ 0)
    (hLI : LinearIndependent ℝ ![collPartialA r a b m, collPartialB r a b m]) :
    AnalyticTrisecantLocalCurve r (a, (b, m)) := by
  let p : RealParamTriple := (a, (b, m))
  let A : ℝ × (ℝ × ℝ) → RealParamTriple := splitAB
  let B : RealParamTriple → ℝ × (ℝ × ℝ) := unSplitAB
  let u : ℝ × (ℝ × ℝ) := (m, (a, b))
  let red : RealParamTriple → ℝ × ℝ := pairReduced r a b m (0 : Fin 3) (1 : Fin 3)
  have hColl : collinearityMap r p = 0 := by
    dsimp [p]
    exact hΦ
  have hOff : p ∈ RealOffDiagonalTriples r := by
    dsimp [p, RealOffDiagonalTriples]
    exact ⟨hZ, hW0, hmb⟩
  have hu : A u = p := by
    dsimp [A, u, p, splitAB]
  have hred0 : red p = (0, 0) := by
    dsimp [red, p]
    exact pairReduced_base_zero a b m (0 : Fin 3) (1 : Fin 3) hΦ
  have hredColl : ∀ q : RealParamTriple, collinearityMap r q = 0 → red q = (0, 0) := by
    intro q hq
    dsimp [red]
    simp [pairReduced, hq]
  have hCdA : ContDiff ℝ ⊤ (red ∘ A) := by
    dsimp [red, A]
    have hc : ContDiff ℝ ⊤ (fun q : RealParamTriple => pairReduced r a b m (0 : Fin 3) (1 : Fin 3) q) :=
      ContDiff.of_le (contDiff_pairReduced h a b m (0 : Fin 3) (1 : Fin 3)) le_top
    exact ContDiff.comp hc (ContDiff.of_le splitAB_contDiff le_top)
  -- the partial derivative along the second factor is the Gram matrix
  let D : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := (fderiv ℝ (red ∘ A) u) ∘L .inr ℝ ℝ (ℝ × ℝ)
  have hcdAat : DifferentiableAt ℝ (red ∘ A) u := by
    have hd : Differentiable ℝ (red ∘ A) := hCdA.differentiable (by norm_num)
    exact hd.differentiableAt
  have hcdR : DifferentiableAt ℝ red (a, (b, m)) := by
    have hd : Differentiable ℝ red :=
      (contDiff_pairReduced h a b m (0 : Fin 3) (1 : Fin 3)).differentiable (by norm_num)
    exact hd.differentiableAt
  have hcol1 : D (1, 0) = (inner ℝ (collPartialA r a b m) (collPartialA r a b m),
      inner ℝ (collPartialA r a b m) (collPartialB r a b m)) := by
    dsimp [D]
    have hline : HasDerivAt (fun s : ℝ => (red ∘ A) (u + s • ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))))
        ((fderiv ℝ (red ∘ A) u) ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))) 0 :=
      fderiv_along_axis_eq_deriv (H := red ∘ A) (p := u) (e := ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))) hcdAat
    have hpath : (fun s : ℝ => (red ∘ A) (u + s • ((0 : ℝ), ((1 : ℝ), (0 : ℝ))))) =
        fun s : ℝ => red (a + s, (b, m)) := by
      funext s
      change red (A ((m, (a, b)) + s • ((0 : ℝ), ((1 : ℝ), (0 : ℝ))))) = red (a + s, (b, m))
      congr 1
      dsimp [A, u, splitAB]
      simp
    have hg' : HasDerivAt (fun s : ℝ => red (a + s, (b, m)))
        ((fderiv ℝ (red ∘ A) u) ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))) 0 := by
      rw [hpath] at hline
      exact hline
    have hlineR : HasDerivAt (fun s : ℝ => red ((a, (b, m)) + s • axisVec (0 : Fin 3)))
        ((fderiv ℝ red (a, (b, m))) (axisVec (0 : Fin 3))) 0 :=
      fderiv_along_axis_eq_deriv (H := red) (p := (a, (b, m))) (e := axisVec (0 : Fin 3)) hcdR
    have hpathR : (fun s : ℝ => red (a + s, (b, m))) = fun s : ℝ => red ((a, (b, m)) + s • axisVec (0 : Fin 3)) := by
      funext s
      congr 1
      dsimp [axisVec]
      ext <;> simp
    have hlineR' : HasDerivAt (fun s : ℝ => red (a + s, (b, m)))
        ((fderiv ℝ red (a, (b, m))) (axisVec (0 : Fin 3))) 0 := by
      rw [← hpathR] at hlineR
      exact hlineR
    have huniq := HasDerivAt.unique hlineR' hg'
    have hcol : (fderiv ℝ red (a, (b, m))) (axisVec (0 : Fin 3)) =
        (inner ℝ (collPartialA r a b m) (collPartialA r a b m),
          inner ℝ (collPartialA r a b m) (collPartialB r a b m)) := by
      dsimp [red]
      simpa [collPartial_eq_A, collPartial_eq_B] using
        (fderiv_pairReduced_axis h a b m (0 : Fin 3) (0 : Fin 3) (1 : Fin 3))
    rw [hcol] at huniq
    simpa [ContinuousLinearMap.comp_apply] using huniq.symm
  have hcol2 : D (0, 1) = (inner ℝ (collPartialB r a b m) (collPartialA r a b m),
      inner ℝ (collPartialB r a b m) (collPartialB r a b m)) := by
    dsimp [D]
    have hline : HasDerivAt (fun s : ℝ => (red ∘ A) (u + s • ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))))
        ((fderiv ℝ (red ∘ A) u) ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) 0 :=
      fderiv_along_axis_eq_deriv (H := red ∘ A) (p := u) (e := ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) hcdAat
    have hpath : (fun s : ℝ => (red ∘ A) (u + s • ((0 : ℝ), ((0 : ℝ), (1 : ℝ))))) =
        fun s : ℝ => red (a, (b + s, m)) := by
      funext s
      change red (A ((m, (a, b)) + s • ((0 : ℝ), ((0 : ℝ), (1 : ℝ))))) = red (a, (b + s, m))
      congr 1
      dsimp [A, u, splitAB]
      simp
    have hg' : HasDerivAt (fun s : ℝ => red (a, (b + s, m)))
        ((fderiv ℝ (red ∘ A) u) ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) 0 := by
      rw [hpath] at hline
      exact hline
    have hlineR : HasDerivAt (fun s : ℝ => red ((a, (b, m)) + s • axisVec (1 : Fin 3)))
        ((fderiv ℝ red (a, (b, m))) (axisVec (1 : Fin 3))) 0 :=
      fderiv_along_axis_eq_deriv (H := red) (p := (a, (b, m))) (e := axisVec (1 : Fin 3)) hcdR
    have hpathR : (fun s : ℝ => red (a, (b + s, m))) = fun s : ℝ => red ((a, (b, m)) + s • axisVec (1 : Fin 3)) := by
      funext s
      congr 1
      dsimp [axisVec]
      ext <;> simp
    have hlineR' : HasDerivAt (fun s : ℝ => red (a, (b + s, m)))
        ((fderiv ℝ red (a, (b, m))) (axisVec (1 : Fin 3))) 0 := by
      rw [← hpathR] at hlineR
      exact hlineR
    have huniq := HasDerivAt.unique hlineR' hg'
    have hcol : (fderiv ℝ red (a, (b, m))) (axisVec (1 : Fin 3)) =
        (inner ℝ (collPartialB r a b m) (collPartialA r a b m),
          inner ℝ (collPartialB r a b m) (collPartialB r a b m)) := by
      dsimp [red]
      simpa [collPartial_eq_A, collPartial_eq_B] using
        (fderiv_pairReduced_axis h a b m (1 : Fin 3) (0 : Fin 3) (1 : Fin 3))
    rw [hcol] at huniq
    simpa [ContinuousLinearMap.comp_apply] using huniq.symm
  -- invertibility of the partial derivative: Gram determinant is nonzero
  have hgram : (Matrix.det !![inner ℝ (collPartialA r a b m) (collPartialA r a b m),
        inner ℝ (collPartialA r a b m) (collPartialB r a b m);
        inner ℝ (collPartialB r a b m) (collPartialA r a b m),
        inner ℝ (collPartialB r a b m) (collPartialB r a b m)]) ≠ 0 := by
    exact Commons.Analysis.InnerProductSpace.gram_det_ne_zero_of_linearIndependent hLI
  have if₂ : D.IsInvertible := by
    exact Commons.Analysis.Normed.isInvertible_of_det_columns (D := D) (c₁₁ := inner ℝ (collPartialA r a b m) (collPartialA r a b m))
      (c₁₂ := inner ℝ (collPartialA r a b m) (collPartialB r a b m))
      (c₂₁ := inner ℝ (collPartialB r a b m) (collPartialA r a b m))
      (c₂₂ := inner ℝ (collPartialB r a b m) (collPartialB r a b m))
      (hc₁ := hcol1) (hc₂ := hcol2) (hdet := by
        have hEq : (Matrix.det !![inner ℝ (collPartialA r a b m) (collPartialA r a b m),
              inner ℝ (collPartialA r a b m) (collPartialB r a b m);
              inner ℝ (collPartialB r a b m) (collPartialA r a b m),
              inner ℝ (collPartialB r a b m) (collPartialB r a b m)])
            = (inner ℝ (collPartialA r a b m) (collPartialA r a b m)) *
                (inner ℝ (collPartialB r a b m) (collPartialB r a b m)) -
              (inner ℝ (collPartialA r a b m) (collPartialB r a b m)) *
                (inner ℝ (collPartialB r a b m) (collPartialA r a b m)) := by
          rw [Matrix.det_fin_two_of]
        rw [← hEq]
        exact hgram)
  -- identification of the zero sets
  have hidentAB : ∃ U : Set RealParamTriple, IsOpen U ∧ p ∈ U ∧
      ∀ q ∈ U, red q = (0, 0) → collinearityMap r q = 0 := by
    simpa [red] using (identification_pairReduced_zero h a b m (0 : Fin 3) (1 : Fin 3) hΦ hZ
      (by simpa [collPartial_eq_A, collPartial_eq_B] using hLI))
  exact analyticTrisecantLocalCurve_of_splitData (r := r) h p hColl hOff A B splitAB_contDiff
    unSplitAB_continuous unSplitAB_splitAB splitAB_unSplitAB u hu red hCdA hred0 hredColl if₂ hidentAB


theorem analyticLocalSmoothCurve_AM {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ)
    (hΦ : collinearityValue r a b m = 0)
    (hZ : r a - r b ≠ 0) (hW0 : r a - r m ≠ 0) (hmb : r m - r b ≠ 0)
    (hLI : LinearIndependent ℝ ![collPartialA r a b m, collPartialM r a b m]) :
    AnalyticTrisecantLocalCurve r (a, (b, m)) := by
  let p : RealParamTriple := (a, (b, m))
  let A : ℝ × (ℝ × ℝ) → RealParamTriple := splitAM
  let B : RealParamTriple → ℝ × (ℝ × ℝ) := unSplitAM
  let u : ℝ × (ℝ × ℝ) := (b, (a, m))
  let red : RealParamTriple → ℝ × ℝ := fun q => pairReduced r a b m (0 : Fin 3) (2 : Fin 3) q
  have hColl : collinearityMap r p = 0 := by dsimp [p]; exact hΦ
  have hOff : p ∈ RealOffDiagonalTriples r := by
    dsimp [p, RealOffDiagonalTriples]
    exact ⟨hZ, hW0, hmb⟩
  have hu : A u = p := by
    dsimp [A, u, p, splitAM]
  have hred0 : red p = (0, 0) := by
    dsimp [red, p]
    exact pairReduced_base_zero a b m (0 : Fin 3) (2 : Fin 3) hΦ
  have hredColl : ∀ q : RealParamTriple, collinearityMap r q = 0 → red q = (0, 0) := by
    intro q hq
    dsimp [red]
    simp [pairReduced, hq]
  have hred : red = fun q : RealParamTriple => pairReduced r a b m (0 : Fin 3) (2 : Fin 3) q := rfl
  have hp0 : (a, (b, m)) = (a, (b, m)) := rfl
  have hCdA : ContDiff ℝ ⊤ (red ∘ A) := by
    dsimp [red, A]
    have hc : ContDiff ℝ ⊤ (fun q : RealParamTriple => pairReduced r a b m (0 : Fin 3) (2 : Fin 3) q) :=
      ContDiff.of_le (contDiff_pairReduced h a b m (0 : Fin 3) (2 : Fin 3)) le_top
    exact ContDiff.comp hc (ContDiff.of_le splitAM_contDiff le_top)
  have hcdAat : DifferentiableAt ℝ (red ∘ A) u := by
    have hd : Differentiable ℝ (red ∘ A) := hCdA.differentiable (by norm_num)
    exact hd.differentiableAt
  let D : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := (fderiv ℝ (red ∘ A) u) ∘L .inr ℝ ℝ (ℝ × ℝ)
  have hpath1 : (fun s : ℝ => (red ∘ A) (u + s • ((0 : ℝ), ((1 : ℝ), (0 : ℝ))))) =
      fun s : ℝ => red (a + s, (b, m)) := by
    funext s
    change red (A ((b, (a, m)) + s • ((0 : ℝ), ((1 : ℝ), (0 : ℝ))))) = red (a + s, (b, m))
    congr 1
    dsimp [A, u, splitAM]
    simp
  have hd1 : HasDerivAt (fun s : ℝ => red (a + s, (b, m)))
      (inner ℝ (collPartial r a b m (0 : Fin 3)) (collPartial r a b m (0 : Fin 3)),
        inner ℝ (collPartial r a b m (0 : Fin 3)) (collPartial r a b m (2 : Fin 3))) 0 := by
    exact axis_path_col h a b m (0 : Fin 3) (2 : Fin 3) (0 : Fin 3) red hred (a, (b, m)) rfl
      (fun s : ℝ => (a + s, (b, m))) (by funext s; dsimp [axisVec]; ext <;> ring)
  have hcol1 : D (1, 0) = (inner ℝ (collPartialA r a b m) (collPartialA r a b m),
      inner ℝ (collPartialA r a b m) (collPartialM r a b m)) := by
    dsimp [D]
    have hc := split_col_helper (red := red) (A := A) (u := u) (d := ((1 : ℝ), (0 : ℝ)))
      (path := fun s : ℝ => (a + s, (b, m))) (col := (inner ℝ (collPartialA r a b m) (collPartialA r a b m),
        inner ℝ (collPartialA r a b m) (collPartialM r a b m))) hcdAat hpath1
      (by simpa [collPartial_eq_A, collPartial_eq_M] using hd1)
    simpa using hc
  have hpath2 : (fun s : ℝ => (red ∘ A) (u + s • ((0 : ℝ), ((0 : ℝ), (1 : ℝ))))) =
      fun s : ℝ => red (a, (b, m + s)) := by
    funext s
    change red (A ((b, (a, m)) + s • ((0 : ℝ), ((0 : ℝ), (1 : ℝ))))) = red (a, (b, m + s))
    congr 1
    dsimp [A, u, splitAM]
    simp
  have hd2 : HasDerivAt (fun s : ℝ => red (a, (b, m + s)))
      (inner ℝ (collPartial r a b m (2 : Fin 3)) (collPartial r a b m (0 : Fin 3)),
        inner ℝ (collPartial r a b m (2 : Fin 3)) (collPartial r a b m (2 : Fin 3))) 0 := by
    exact axis_path_col h a b m (0 : Fin 3) (2 : Fin 3) (2 : Fin 3) red hred (a, (b, m)) rfl
      (fun s : ℝ => (a, (b, m + s))) (by funext s; dsimp [axisVec]; ext <;> ring)
  have hcol2 : D (0, 1) = (inner ℝ (collPartialM r a b m) (collPartialA r a b m),
      inner ℝ (collPartialM r a b m) (collPartialM r a b m)) := by
    dsimp [D]
    have hc := split_col_helper (red := red) (A := A) (u := u) (d := ((0 : ℝ), (1 : ℝ)))
      (path := fun s : ℝ => (a, (b, m + s))) (col := (inner ℝ (collPartialM r a b m) (collPartialA r a b m),
        inner ℝ (collPartialM r a b m) (collPartialM r a b m))) hcdAat hpath2
      (by simpa [collPartial_eq_A, collPartial_eq_M] using hd2)
    simpa using hc
  have hgram : (Matrix.det !![inner ℝ (collPartialA r a b m) (collPartialA r a b m),
        inner ℝ (collPartialA r a b m) (collPartialM r a b m);
        inner ℝ (collPartialM r a b m) (collPartialA r a b m),
        inner ℝ (collPartialM r a b m) (collPartialM r a b m)]) ≠ 0 := by
    exact Commons.Analysis.InnerProductSpace.gram_det_ne_zero_of_linearIndependent hLI
  have if₂ : D.IsInvertible := by
    exact Commons.Analysis.Normed.isInvertible_of_det_columns (D := D)
      (c₁₁ := inner ℝ (collPartialA r a b m) (collPartialA r a b m))
      (c₁₂ := inner ℝ (collPartialA r a b m) (collPartialM r a b m))
      (c₂₁ := inner ℝ (collPartialM r a b m) (collPartialA r a b m))
      (c₂₂ := inner ℝ (collPartialM r a b m) (collPartialM r a b m))
      (hc₁ := hcol1) (hc₂ := hcol2) (hdet := by
        have hEq : (Matrix.det !![inner ℝ (collPartialA r a b m) (collPartialA r a b m),
              inner ℝ (collPartialA r a b m) (collPartialM r a b m);
              inner ℝ (collPartialM r a b m) (collPartialA r a b m),
              inner ℝ (collPartialM r a b m) (collPartialM r a b m)])
            = (inner ℝ (collPartialA r a b m) (collPartialA r a b m)) *
                (inner ℝ (collPartialM r a b m) (collPartialM r a b m)) -
              (inner ℝ (collPartialA r a b m) (collPartialM r a b m)) *
                (inner ℝ (collPartialM r a b m) (collPartialA r a b m)) := by
          rw [Matrix.det_fin_two_of]
        rw [← hEq]
        exact hgram)
  have hidentAM : ∃ U : Set RealParamTriple, IsOpen U ∧ p ∈ U ∧
      ∀ q ∈ U, red q = (0, 0) → collinearityMap r q = 0 := by
    simpa [red] using (identification_pairReduced_zero h a b m (0 : Fin 3) (2 : Fin 3) hΦ hZ
      (by simpa [collPartial_eq_A, collPartial_eq_M] using hLI))
  exact analyticTrisecantLocalCurve_of_splitData (r := r) h p hColl hOff A B splitAM_contDiff
    unSplitAM_continuous unSplitAM_splitAM splitAM_unSplitAM u hu red hCdA hred0 hredColl if₂ hidentAM

theorem analyticLocalSmoothCurve_BM {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ)
    (hΦ : collinearityValue r a b m = 0)
    (hZ : r a - r b ≠ 0) (hW0 : r a - r m ≠ 0) (hmb : r m - r b ≠ 0)
    (hLI : LinearIndependent ℝ ![collPartialB r a b m, collPartialM r a b m]) :
    AnalyticTrisecantLocalCurve r (a, (b, m)) := by
  let p : RealParamTriple := (a, (b, m))
  let A : ℝ × (ℝ × ℝ) → RealParamTriple := splitBM
  let B : RealParamTriple → ℝ × (ℝ × ℝ) := unSplitBM
  let u : ℝ × (ℝ × ℝ) := (a, (b, m))
  let red : RealParamTriple → ℝ × ℝ := fun q => pairReduced r a b m (1 : Fin 3) (2 : Fin 3) q
  have hColl : collinearityMap r p = 0 := by dsimp [p]; exact hΦ
  have hOff : p ∈ RealOffDiagonalTriples r := by
    dsimp [p, RealOffDiagonalTriples]
    exact ⟨hZ, hW0, hmb⟩
  have hu : A u = p := by
    dsimp [A, u, p, splitBM]
  have hred0 : red p = (0, 0) := by
    dsimp [red, p]
    exact pairReduced_base_zero a b m (1 : Fin 3) (2 : Fin 3) hΦ
  have hredColl : ∀ q : RealParamTriple, collinearityMap r q = 0 → red q = (0, 0) := by
    intro q hq
    dsimp [red]
    simp [pairReduced, hq]
  have hred : red = fun q : RealParamTriple => pairReduced r a b m (1 : Fin 3) (2 : Fin 3) q := rfl
  have hCdA : ContDiff ℝ ⊤ (red ∘ A) := by
    dsimp [red, A]
    have hc : ContDiff ℝ ⊤ (fun q : RealParamTriple => pairReduced r a b m (1 : Fin 3) (2 : Fin 3) q) :=
      ContDiff.of_le (contDiff_pairReduced h a b m (1 : Fin 3) (2 : Fin 3)) le_top
    exact ContDiff.comp hc (ContDiff.of_le splitBM_contDiff le_top)
  have hcdAat : DifferentiableAt ℝ (red ∘ A) u := by
    have hd : Differentiable ℝ (red ∘ A) := hCdA.differentiable (by norm_num)
    exact hd.differentiableAt
  let D : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := (fderiv ℝ (red ∘ A) u) ∘L .inr ℝ ℝ (ℝ × ℝ)
  have hpath1 : (fun s : ℝ => (red ∘ A) (u + s • ((0 : ℝ), ((1 : ℝ), (0 : ℝ))))) =
      fun s : ℝ => red (a, (b + s, m)) := by
    funext s
    change red (A ((a, (b, m)) + s • ((0 : ℝ), ((1 : ℝ), (0 : ℝ))))) = red (a, (b + s, m))
    congr 1
    dsimp [A, u, splitBM]
    simp
  have hd1 : HasDerivAt (fun s : ℝ => red (a, (b + s, m)))
      (inner ℝ (collPartial r a b m (1 : Fin 3)) (collPartial r a b m (1 : Fin 3)),
        inner ℝ (collPartial r a b m (1 : Fin 3)) (collPartial r a b m (2 : Fin 3))) 0 := by
    exact axis_path_col h a b m (1 : Fin 3) (2 : Fin 3) (1 : Fin 3) red hred (a, (b, m)) rfl
      (fun s : ℝ => (a, (b + s, m))) (by funext s; dsimp [axisVec]; ext <;> ring)
  have hcol1 : D (1, 0) = (inner ℝ (collPartialB r a b m) (collPartialB r a b m),
      inner ℝ (collPartialB r a b m) (collPartialM r a b m)) := by
    dsimp [D]
    have hc := split_col_helper (red := red) (A := A) (u := u) (d := ((1 : ℝ), (0 : ℝ)))
      (path := fun s : ℝ => (a, (b + s, m))) (col := (inner ℝ (collPartialB r a b m) (collPartialB r a b m),
        inner ℝ (collPartialB r a b m) (collPartialM r a b m))) hcdAat hpath1
      (by simpa [collPartial_eq_B, collPartial_eq_M] using hd1)
    simpa using hc
  have hpath2 : (fun s : ℝ => (red ∘ A) (u + s • ((0 : ℝ), ((0 : ℝ), (1 : ℝ))))) =
      fun s : ℝ => red (a, (b, m + s)) := by
    funext s
    change red (A ((a, (b, m)) + s • ((0 : ℝ), ((0 : ℝ), (1 : ℝ))))) = red (a, (b, m + s))
    congr 1
    dsimp [A, u, splitBM]
    simp
  have hd2 : HasDerivAt (fun s : ℝ => red (a, (b, m + s)))
      (inner ℝ (collPartial r a b m (2 : Fin 3)) (collPartial r a b m (1 : Fin 3)),
        inner ℝ (collPartial r a b m (2 : Fin 3)) (collPartial r a b m (2 : Fin 3))) 0 := by
    exact axis_path_col h a b m (1 : Fin 3) (2 : Fin 3) (2 : Fin 3) red hred (a, (b, m)) rfl
      (fun s : ℝ => (a, (b, m + s))) (by funext s; dsimp [axisVec]; ext <;> ring)
  have hcol2 : D (0, 1) = (inner ℝ (collPartialM r a b m) (collPartialB r a b m),
      inner ℝ (collPartialM r a b m) (collPartialM r a b m)) := by
    dsimp [D]
    have hc := split_col_helper (red := red) (A := A) (u := u) (d := ((0 : ℝ), (1 : ℝ)))
      (path := fun s : ℝ => (a, (b, m + s))) (col := (inner ℝ (collPartialM r a b m) (collPartialB r a b m),
        inner ℝ (collPartialM r a b m) (collPartialM r a b m))) hcdAat hpath2
      (by simpa [collPartial_eq_B, collPartial_eq_M] using hd2)
    simpa using hc
  have hgram : (Matrix.det !![inner ℝ (collPartialB r a b m) (collPartialB r a b m),
        inner ℝ (collPartialB r a b m) (collPartialM r a b m);
        inner ℝ (collPartialM r a b m) (collPartialB r a b m),
        inner ℝ (collPartialM r a b m) (collPartialM r a b m)]) ≠ 0 := by
    exact Commons.Analysis.InnerProductSpace.gram_det_ne_zero_of_linearIndependent hLI
  have if₂ : D.IsInvertible := by
    exact Commons.Analysis.Normed.isInvertible_of_det_columns (D := D)
      (c₁₁ := inner ℝ (collPartialB r a b m) (collPartialB r a b m))
      (c₁₂ := inner ℝ (collPartialB r a b m) (collPartialM r a b m))
      (c₂₁ := inner ℝ (collPartialM r a b m) (collPartialB r a b m))
      (c₂₂ := inner ℝ (collPartialM r a b m) (collPartialM r a b m))
      (hc₁ := hcol1) (hc₂ := hcol2) (hdet := by
        have hEq : (Matrix.det !![inner ℝ (collPartialB r a b m) (collPartialB r a b m),
              inner ℝ (collPartialB r a b m) (collPartialM r a b m);
              inner ℝ (collPartialM r a b m) (collPartialB r a b m),
              inner ℝ (collPartialM r a b m) (collPartialM r a b m)])
            = (inner ℝ (collPartialB r a b m) (collPartialB r a b m)) *
                (inner ℝ (collPartialM r a b m) (collPartialM r a b m)) -
              (inner ℝ (collPartialB r a b m) (collPartialM r a b m)) *
                (inner ℝ (collPartialM r a b m) (collPartialB r a b m)) := by
          rw [Matrix.det_fin_two_of]
        rw [← hEq]
        exact hgram)
  have hidentBM : ∃ U : Set RealParamTriple, IsOpen U ∧ p ∈ U ∧
      ∀ q ∈ U, red q = (0, 0) → collinearityMap r q = 0 := by
    simpa [red] using (identification_pairReduced_zero h a b m (1 : Fin 3) (2 : Fin 3) hΦ hZ
      (by simpa [collPartial_eq_B, collPartial_eq_M] using hLI))
  exact analyticTrisecantLocalCurve_of_splitData (r := r) h p hColl hOff A B splitBM_contDiff
    unSplitBM_continuous unSplitBM_splitBM splitBM_unSplitBM u hu red hCdA hred0 hredColl if₂ hidentBM

theorem smooth_local_curve_of_general_position (r : ℝ → Space) (h : IsSmoothKnot r) :
    AnalyticLocalSmoothCurveTheorem r := by
  intro a b m hGP hΦ
  rcases hGP with ⟨hZ, hW, hmb, hP⟩
  rcases hP with ⟨i, j, hij, hLIij⟩
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact analyticLocalSmoothCurve_AB h a b m hΦ hZ hW hmb
      (by simpa [collPartial_eq_A, collPartial_eq_B] using hLIij)
  · exact analyticLocalSmoothCurve_AM h a b m hΦ hZ hW hmb
      (by simpa [collPartial_eq_A, collPartial_eq_M] using hLIij)
  · exact analyticLocalSmoothCurve_AB h a b m hΦ hZ hW hmb
      (by
        have hsw := (linearIndependent_pair_swap_iff (collPartialA r a b m) (collPartialB r a b m)).mp ?_
        · simpa [collPartial_eq_A, collPartial_eq_B] using hsw
        · simpa [collPartial_eq_A, collPartial_eq_B] using hLIij)
  · exact False.elim (hij rfl)
  · exact analyticLocalSmoothCurve_BM h a b m hΦ hZ hW hmb
      (by simpa [collPartial_eq_B, collPartial_eq_M] using hLIij)
  · exact analyticLocalSmoothCurve_AM h a b m hΦ hZ hW hmb
      (by
        have hsw := (linearIndependent_pair_swap_iff (collPartialA r a b m) (collPartialM r a b m)).mp ?_
        · simpa [collPartial_eq_A, collPartial_eq_M] using hsw
        · simpa [collPartial_eq_A, collPartial_eq_M] using hLIij)
  · exact analyticLocalSmoothCurve_BM h a b m hΦ hZ hW hmb
      (by
        have hsw := (linearIndependent_pair_swap_iff (collPartialB r a b m) (collPartialM r a b m)).mp ?_
        · simpa [collPartial_eq_B, collPartial_eq_M] using hsw
        · simpa [collPartial_eq_B, collPartial_eq_M] using hLIij)
  · exact False.elim (hij rfl)

/-- **The analytic local-curve theorem.**  At every general-position collinear off-diagonal
triple of a smooth knot, the off-diagonal zero set of the collinearity map has, locally at the
triple, the structure of an injective *analytic* curve through the triple. -/
theorem analyticLocalCurve (r : ℝ → Space) (h : IsSmoothKnot r) :
    Work.Drive.AnalyticLocalSmoothCurveTheorem r :=
  smooth_local_curve_of_general_position r h

end Work.Drive

end
