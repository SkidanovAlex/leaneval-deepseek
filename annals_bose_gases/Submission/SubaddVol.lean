import Mathlib
import ChallengeDeps
import Submission.PairsSplit
import Submission.PotSupport
import Submission.Potential
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Layer 2 — comparison inequalities for the finite-volume energy, part 2:
subadditivity over separated volumes.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped ContDiff Topology Real
open MeasureTheory InnerProductSpace

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)


local notation "𝓗" => _root_.BoseGases.𝓗

/-! ## Coordinate split `Fin (N1+N2) ≃ Fin N1 ⊕ Fin N2` -/

/-- The equivalence splitting `Fin (N1+N2)` into `Fin N1 ⊕ Fin N2` (first `N1` vs last `N2`). -/
def finSplit (N1 N2 : ℕ) : Fin (N1 + N2) ≃ Fin N1 ⊕ Fin N2 :=
  (finSumFinEquiv (m := N1) (n := N2)).symm

@[simp] lemma finSplit_castAdd (N1 N2 : ℕ) (i : Fin N1) :
    finSplit N1 N2 (Fin.castAdd N2 i) = Sum.inl i := by
  simp [finSplit]

@[simp] lemma finSplit_natAdd (N1 N2 : ℕ) (j : Fin N2) :
    finSplit N1 N2 (Fin.natAdd N1 j) = Sum.inr j := by
  simp [finSplit]

/-- The first `N1` coordinates of a configuration of `N1+N2` particles. -/
def firstBlock (N1 N2 : ℕ) : X (N1+N2) → X N1 := fun x i => x (Fin.castAdd N2 i)

/-- The last `N2` coordinates of a configuration of `N1+N2` particles. -/
def lastBlock (N1 N2 : ℕ) : X (N1+N2) → X N2 := fun x j => x (Fin.natAdd N1 j)

/-- The inverse of `(firstBlock, lastBlock)`. -/
def mergeBlock (N1 N2 : ℕ) : X N1 × X N2 → X (N1+N2) :=
  fun p k => Sum.elim p.1 p.2 (finSplit N1 N2 k)

lemma mergeBlock_first (N1 N2 : ℕ) (x : X N1) (y : X N2) :
    firstBlock N1 N2 (mergeBlock N1 N2 (x, y)) = x := by
  ext i
  simp [mergeBlock, firstBlock]

lemma mergeBlock_last (N1 N2 : ℕ) (x : X N1) (y : X N2) :
    lastBlock N1 N2 (mergeBlock N1 N2 (x, y)) = y := by
  ext j
  simp [mergeBlock, lastBlock]

lemma mergeBlock_eq (N1 N2 : ℕ) (z : X (N1+N2)) :
    mergeBlock N1 N2 (firstBlock N1 N2 z, lastBlock N1 N2 z) = z := by
  ext k
  by_cases h : k.val < N1
  · let i : Fin N1 := ⟨k.val, h⟩
    have hk : k = Fin.castAdd N2 i := by
      ext; simp [i]
    simp [mergeBlock, firstBlock, lastBlock, hk]
  · let j : Fin N2 := ⟨k.val - N1, by omega⟩
    have hk : k = Fin.natAdd N1 j := by
      ext; simp [j]; omega
    simp [mergeBlock, firstBlock, lastBlock, hk]

/-! ## Update of the two blocks commutes with coordinate updates -/

lemma firstBlock_update (N1 N2 : ℕ) (x : X (N1+N2)) (i1 : Fin N1) (z : ℝ³) :
    firstBlock N1 N2 (Function.update x (Fin.castAdd N2 i1) z) =
      Function.update (firstBlock N1 N2 x) i1 z := by
  ext i
  by_cases h : i = i1
  · subst i; simp [firstBlock]
  · have : Fin.castAdd N2 i ≠ Fin.castAdd N2 i1 := by
      intro hc
      apply h
      have hi := congrArg Fin.val hc
      simp at hi
      exact Fin.ext hi
    simp [firstBlock, h, this]

lemma lastBlock_update_first (N1 N2 : ℕ) (x : X (N1+N2)) (i1 : Fin N1) (z : ℝ³) :
    lastBlock N1 N2 (Function.update x (Fin.castAdd N2 i1) z) = lastBlock N1 N2 x := by
  ext j
  have : Fin.natAdd N1 j ≠ Fin.castAdd N2 i1 := by
    intro hc
    have hval := congrArg Fin.val hc
    have : N1 ≤ (Fin.natAdd N1 j).val := by simp
    have : (Fin.castAdd N2 i1).val < N1 := by simp
    omega
  simp [lastBlock, this]

lemma firstBlock_update_last (N1 N2 : ℕ) (x : X (N1+N2)) (j2 : Fin N2) (z : ℝ³) :
    firstBlock N1 N2 (Function.update x (Fin.natAdd N1 j2) z) = firstBlock N1 N2 x := by
  ext i
  have : Fin.castAdd N2 i ≠ Fin.natAdd N1 j2 := by
    intro hc
    have hval := congrArg Fin.val hc
    have : (Fin.castAdd N2 i).val < N1 := by simp
    have : N1 ≤ (Fin.natAdd N1 j2).val := by simp
    omega
  simp [firstBlock, this]

lemma lastBlock_update_last (N1 N2 : ℕ) (x : X (N1+N2)) (j2 : Fin N2) (z : ℝ³) :
    lastBlock N1 N2 (Function.update x (Fin.natAdd N1 j2) z) =
      Function.update (lastBlock N1 N2 x) j2 z := by
  ext j
  by_cases h : j = j2
  · subst j; simp [lastBlock]
  · have : Fin.natAdd N1 j ≠ Fin.natAdd N1 j2 := by
      intro hc
      apply h
      have hi := congrArg Fin.val hc
      simp at hi
      omega
    simp [lastBlock, h, this]

/-! ## Measure-preserving block-split and change of variables -/

noncomputable def e1 (N1 N2 : ℕ) : X (N1+N2) ≃ᵐ ((Fin N1 ⊕ Fin N2) → ℝ³) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin N1 ⊕ Fin N2 => ℝ³) (finSplit N1 N2)

noncomputable def e2 (N1 N2 : ℕ) : ((Fin N1 ⊕ Fin N2) → ℝ³) ≃ᵐ X N1 × X N2 :=
  MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin N1 ⊕ Fin N2 => ℝ³)

/-- The measurable equivalence `X (N1+N2) ≃ X N1 × X N2`, sending `x` to
`(firstBlock x, lastBlock x)`. -/
noncomputable def blockSplitEquiv (N1 N2 : ℕ) : X (N1+N2) ≃ᵐ (X N1 × X N2) :=
  (e1 N1 N2).trans (e2 N1 N2)

lemma blockSplitEquiv_apply_fst (N1 N2 : ℕ) (x : X (N1+N2)) :
    (blockSplitEquiv N1 N2 x).1 = firstBlock N1 N2 x := by
  rw [show blockSplitEquiv N1 N2 x = e2 N1 N2 (e1 N1 N2 x) by rfl]
  funext i
  change ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin N1 ⊕ Fin N2 => ℝ³)) (e1 N1 N2 x)).1 i = x (Fin.castAdd N2 i)
  simp only [MeasurableEquiv.coe_sumPiEquivProdPi, Equiv.sumPiEquivProdPi_apply]
  change (e1 N1 N2 x) (Sum.inl i) = x (Fin.castAdd N2 i)
  rw [← finSplit_castAdd N1 N2 i]
  exact MeasurableEquiv.piCongrLeft_apply_apply (finSplit N1 N2)
    (β := fun _ : Fin N1 ⊕ Fin N2 => ℝ³) x (Fin.castAdd N2 i)

lemma blockSplitEquiv_apply_snd (N1 N2 : ℕ) (x : X (N1+N2)) :
    (blockSplitEquiv N1 N2 x).2 = lastBlock N1 N2 x := by
  rw [show blockSplitEquiv N1 N2 x = e2 N1 N2 (e1 N1 N2 x) by rfl]
  funext j
  change ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin N1 ⊕ Fin N2 => ℝ³)) (e1 N1 N2 x)).2 j = x (Fin.natAdd N1 j)
  simp only [MeasurableEquiv.coe_sumPiEquivProdPi, Equiv.sumPiEquivProdPi_apply]
  change (e1 N1 N2 x) (Sum.inr j) = x (Fin.natAdd N1 j)
  rw [← finSplit_natAdd N1 N2 j]
  exact MeasurableEquiv.piCongrLeft_apply_apply (finSplit N1 N2)
    (β := fun _ : Fin N1 ⊕ Fin N2 => ℝ³) x (Fin.natAdd N1 j)

lemma blockSplitEquiv_apply (N1 N2 : ℕ) (x : X (N1+N2)) :
    blockSplitEquiv N1 N2 x = (firstBlock N1 N2 x, lastBlock N1 N2 x) := by
  apply Prod.ext
  · exact blockSplitEquiv_apply_fst N1 N2 x
  · exact blockSplitEquiv_apply_snd N1 N2 x

lemma blockSplitEquiv_measurePreserving (N1 N2 : ℕ) : MeasurePreserving (blockSplitEquiv N1 N2) := by
  have h1 : MeasurePreserving (⇑(e1 N1 N2))
      (volume : Measure (X (N1+N2))) (volume : Measure ((Fin N1 ⊕ Fin N2) → ℝ³)) := by
    simpa [e1] using (volume_measurePreserving_piCongrLeft
      (α := fun _ : Fin N1 ⊕ Fin N2 => ℝ³) (f := finSplit N1 N2))
  have h2 : MeasurePreserving (⇑(e2 N1 N2))
      (volume : Measure ((Fin N1 ⊕ Fin N2) → ℝ³)) (volume : Measure (X N1 × X N2)) := by
    simpa [e2] using (volume_measurePreserving_sumPiEquivProdPi
      (X := fun _ : Fin N1 ⊕ Fin N2 => ℝ³))
  have hc : MeasurePreserving (fun x : X (N1+N2) => e2 N1 N2 (e1 N1 N2 x))
      (volume : Measure (X (N1+N2))) (volume : Measure (X N1 × X N2)) := MeasurePreserving.comp h2 h1
  convert hc using 1
  all_goals first | rfl | (ext x <;> rfl)

/-- Whole-space change of variables: `∫_x g (first x, last x) = ∫_{(u,w)} g (u,w)`. -/
lemma integral_split_whole {N1 N2 : ℕ} (g : X N1 × X N2 → ℝ) :
    (∫ x : X (N1+N2), g (firstBlock N1 N2 x, lastBlock N1 N2 x)) = ∫ p : X N1 × X N2, g p := by
  have hpt : (fun x : X (N1+N2) => g (blockSplitEquiv N1 N2 x)) =
      fun x => g (firstBlock N1 N2 x, lastBlock N1 N2 x) := by
    funext x
    rw [blockSplitEquiv_apply]
  rw [← hpt]
  exact (blockSplitEquiv_measurePreserving N1 N2).integral_comp
    (blockSplitEquiv N1 N2).measurableEmbedding g

/-! ## Scalar calculus: the Laplacian commutes with constants and translations -/

lemma laplacian_const_mul {h : ℝ³ → ℝ} (c : ℝ) {x : ℝ³} (hh : ContDiffAt ℝ 2 h x) :
    Δ (fun z => h z * c) x = Δ h x * c := by
  have hm : Δ (fun z => c • h z) x = c • Δ h x :=
    InnerProductSpace.laplacian_smul (𝕜 := ℝ) (f := h) c hh
  have hpt : (fun z : ℝ³ => h z * c) = fun z => c • h z := by
    funext z
    simp [mul_comm]
  rw [hpt]
  simpa [mul_comm, smul_eq_mul] using hm

lemma laplacian_const_mul' {h : ℝ³ → ℝ} (c : ℝ) {x : ℝ³} (hh : ContDiffAt ℝ 2 h x) :
    Δ (fun z => c * h z) x = c * Δ h x := by
  simpa [mul_comm] using laplacian_const_mul c hh

/-- Laplacian commutes with translations. -/
lemma laplacian_comp_add (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℝ} (a x : E) :
    Δ (fun z : E => f (z + a)) x = Δ f (x + a) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (E := E)
    (f := fun z : E => f (z + a)) (stdOrthonormalBasis ℝ E)]
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (E := E)
    (f := f) (stdOrthonormalBasis ℝ E)]
  simp [iteratedFDeriv_comp_add_right]

lemma laplacian_comp_sub (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℝ} (a x : E) :
    Δ (fun z : E => f (z - a)) x = Δ f (x - a) := by
  simpa [sub_eq_add_neg] using (laplacian_comp_add E (f := f) (-a) x)

/-! ## Product states: Laplacians of a product -/

/-- A product of a function of the first block and a function of the last block. -/
def prodState (N1 N2 : ℕ) (f1 : X N1 → ℝ) (f2 : X N2 → ℝ) : X (N1+N2) → ℝ :=
  fun x => f1 (firstBlock N1 N2 x) * f2 (lastBlock N1 N2 x)

/-- The Laplacian of a product state with respect to a first-block particle. -/
lemma partialLaplacian_prodState_first {N1 N2 : ℕ} {f1 : X N1 → ℝ} {f2 : X N2 → ℝ}
    (h1 : ContDiff ℝ 2 f1) (i1 : Fin N1) (x : X (N1+N2)) :
    partialLaplacian (Fin.castAdd N2 i1) (prodState N1 N2 f1 f2) x =
      partialLaplacian i1 f1 (firstBlock N1 N2 x) * f2 (lastBlock N1 N2 x) := by
  let u : X N1 := firstBlock N1 N2 x
  let v : X N2 := lastBlock N1 N2 x
  have hpt : x (Fin.castAdd N2 i1) = u i1 := by simp [u, firstBlock]
  have hslice : (fun y : ℝ³ => prodState N1 N2 f1 f2 (Function.update x (Fin.castAdd N2 i1) y))
      = fun y : ℝ³ => f1 (Function.update u i1 y) * f2 v := by
    funext y
    simp [prodState, firstBlock_update N1 N2 x i1 y, lastBlock_update_first N1 N2 x i1 y, u, v]
  unfold partialLaplacian
  rw [hpt, hslice]
  have hA : ContDiffAt ℝ 2 (fun y : ℝ³ => f1 (Function.update u i1 y)) (u i1) := by
    exact (bridgeSliceContDiff N1 i1 u h1).contDiffAt
  rw [laplacian_const_mul (c := f2 v) hA]

/-- The Laplacian of a product state with respect to a last-block particle. -/
lemma partialLaplacian_prodState_last {N1 N2 : ℕ} {f1 : X N1 → ℝ} {f2 : X N2 → ℝ}
    (h2 : ContDiff ℝ 2 f2) (j2 : Fin N2) (x : X (N1+N2)) :
    partialLaplacian (Fin.natAdd N1 j2) (prodState N1 N2 f1 f2) x =
      f1 (firstBlock N1 N2 x) * partialLaplacian j2 f2 (lastBlock N1 N2 x) := by
  let u : X N1 := firstBlock N1 N2 x
  let v : X N2 := lastBlock N1 N2 x
  have hpt : x (Fin.natAdd N1 j2) = v j2 := by simp [v, lastBlock]
  have hslice : (fun y : ℝ³ => prodState N1 N2 f1 f2 (Function.update x (Fin.natAdd N1 j2) y))
      = fun y : ℝ³ => f1 u * f2 (Function.update v j2 y) := by
    funext y
    simp [prodState, firstBlock_update_last N1 N2 x j2 y, lastBlock_update_last N1 N2 x j2 y, u, v]
  unfold partialLaplacian
  rw [hpt, hslice]
  have hB : ContDiffAt ℝ 2 (fun y : ℝ³ => f2 (Function.update v j2 y)) (v j2) := by
    exact (bridgeSliceContDiff N2 j2 v h2).contDiffAt
  rw [laplacian_const_mul' (c := f1 u) hB]

/-- `partialLaplacian` commutes with the global translation `x ↦ x - c`. -/
lemma partialLaplacian_translate {N : ℕ} {f : X N → ℝ} (c : X N) (j : Fin N) (x : X N) :
    partialLaplacian j (fun y : X N => f (y - c)) x = partialLaplacian j f (x - c) := by
  have hs : (fun z : ℝ³ => f ((Function.update x j z) - c)) =
      fun z : ℝ³ => f (Function.update (x - c) j (z - c j)) := by
    funext z
    congr 1
    ext i
    by_cases h : i = j <;> simp [Function.update, h]
  calc
    partialLaplacian j (fun y : X N => f (y - c)) x
        = Δ (fun z => f ((Function.update x j z) - c)) (x j) := rfl
    _ = Δ (fun z => f (Function.update (x - c) j (z - c j))) (x j) := by rw [hs]
    _ = Δ (fun u : ℝ³ => f (Function.update (x - c) j u)) (x j - c j) := by
          simpa using (laplacian_comp_sub ℝ³ (f := fun u : ℝ³ => f (Function.update (x - c) j u))
            (a := c j) (x := x j))
    _ = partialLaplacian j f (x - c) := rfl

/-! ## The offset vector and the translated second state -/

/-- The vector with every coordinate equal to `d`. -/
def offVec (d : ℝ) : ℝ³ := WithLp.toLp 2 (fun _ : Fin 3 => d)

/-- The global translation of an `N`-particle configuration by the vector `-offVec d`
(the state of a box of side `L2` is shifted so that its box becomes `[L-L2,L]³`). -/
def addShift (N : ℕ) (d : ℝ) : X N → X N := fun w => w + (fun _ : Fin N => -offVec d)

/-- `addShift` is measure-preserving (translation invariance of Lebesgue measure). -/
lemma addShift_measurePreserving (N : ℕ) (d : ℝ) :
    MeasurePreserving (addShift N d) := by
  unfold addShift
  exact measurePreserving_add_right (μ := (volume : Measure (X N))) (-(fun _ : Fin N => offVec d))

/-- The translated state (place the state of the box of side `L2` into the far corner). -/
def shifted (N : ℕ) (d : ℝ) (f : X N → ℝ) : X N → ℝ := fun w => f (addShift N d w)

lemma shifted_contDiff {N : ℕ} {d : ℝ} {f : X N → ℝ} {n : ℕ∞ω} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (shifted N d f) := by
  have hshift : ContDiff ℝ n (addShift N d) := by
    unfold addShift
    exact ContDiff.add contDiff_id contDiff_const
  exact hf.comp hshift

/-! ## Separation geometry of the two corner cubes -/

/-- Any coordinate of a vector is bounded by its norm. -/
lemma abs_coord_le_norm (z : ℝ³) (k : Fin 3) : |(z k)| ≤ ‖z‖ := by
  have hsq : (z k) ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.single_le_sum (fun m hm => sq_nonneg _) (Finset.mem_univ k)
  have hsq' : |(z k)| ^ 2 ≤ ‖z‖ ^ 2 := by rwa [sq_abs]
  exact le_of_sq_le_sq hsq' (norm_nonneg z)

/-- If every coordinate difference `(b k) - (a k)` is at least `R ≥ 0`, then
`‖b - a‖ ≥ R`. -/
lemma norm_ge_of_coord_diff_ge {R : ℝ} {a b : ℝ³} (hR : 0 ≤ R)
    (h : ∀ k : Fin 3, R ≤ (b k) - (a k)) : R ≤ ‖b - a‖ := by
  let k : Fin 3 := 0
  have hk : R ≤ (b k) - (a k) := h k
  have hpos : 0 ≤ (b k) - (a k) := le_trans hR hk
  have habs : R ≤ |(b k) - (a k)| := by
    rwa [abs_of_nonneg hpos]
  have hnorm : |(b k) - (a k)| ≤ ‖b - a‖ := by
    simpa using (abs_coord_le_norm (b - a) k)
  exact le_trans habs hnorm

/-- Points of the origin cube `[0,L1]³` and of the far cube `[L-L2,L]³` (with
`L1 + L2 + R ≤ L`) are at distance at least `R`. -/
lemma dist_ge_of_cubes {L1 L2 R L : ℝ} (hR : 0 ≤ R) (hsep : L1 + L2 + R ≤ L)
    {a b : ℝ³} (ha : ∀ k : Fin 3, (a k) ∈ Set.Icc 0 L1)
    (hb : ∀ k : Fin 3, (b k) ∈ Set.Icc (L - L2) L) : R ≤ ‖b - a‖ := by
  apply norm_ge_of_coord_diff_ge hR
  intro k
  have hk1 : L - L2 ≤ (b k) := (hb k).1
  have hk2 : (a k) ≤ L1 := (ha k).2
  linarith

/-- The nonzero set of a state is open. -/
lemma support_open {N : ℕ} {L : ℝ} (Φ : CInfty0Box N L) :
    IsOpen (Function.support (Φ : X N → ℝ)) := by
  have hcont : Continuous (Φ : X N → ℝ) := (psi_contDiff Φ).continuous
  exact hcont.isOpen_support


/-! ## The trial state -/

noncomputable def fstCLM (N1 N2 : ℕ) : X (N1+N2) →L[ℝ] X N1 :=
  { toFun := firstBlock N1 N2
    map_add' := by intro x y; ext i; rfl
    map_smul' := by intro a x; ext i; rfl
    cont := by
      rw [continuous_pi_iff]
      intro i
      exact continuous_apply (Fin.castAdd N2 i) }

noncomputable def lstCLM (N1 N2 : ℕ) : X (N1+N2) →L[ℝ] X N2 :=
  { toFun := lastBlock N1 N2
    map_add' := by intro x y; ext i; rfl
    map_smul' := by intro a x; ext i; rfl
    cont := by
      rw [continuous_pi_iff]
      intro j
      exact continuous_apply (Fin.natAdd N1 j) }

lemma firstBlock_continuous (N1 N2 : ℕ) : Continuous (firstBlock N1 N2) := (fstCLM N1 N2).cont
lemma lastBlock_continuous (N1 N2 : ℕ) : Continuous (lastBlock N1 N2) := (lstCLM N1 N2).cont
lemma addShift_continuous (N : ℕ) (d : ℝ) : Continuous (addShift N d) := by
  unfold addShift
  fun_prop

/-- The trial state: `Φ1` on the first block (origin corner), the translation of `Φ2`
to the far corner on the last block. -/
noncomputable def trialFun (N1 N2 : ℕ) {L L1 L2 : ℝ} (Φ1 : CInfty0Box N1 L1)
    (Φ2 : CInfty0Box N2 L2) : X (N1+N2) → ℝ :=
  prodState N1 N2 (Φ1 : X N1 → ℝ) (shifted N2 (L - L2) (Φ2 : X N2 → ℝ))

lemma contDiff_trialFun {N1 N2 : ℕ} {L L1 L2 : ℝ} (Φ1 : CInfty0Box N1 L1)
    (Φ2 : CInfty0Box N2 L2) :
    ContDiff ℝ ∞ (trialFun N1 N2 (L := L) (L1 := L1) (L2 := L2) Φ1 Φ2) := by
  unfold trialFun prodState
  have h1 : ContDiff ℝ ∞ (fun x : X (N1+N2) => (Φ1 : X N1 → ℝ) (firstBlock N1 N2 x)) :=
    (psi_contDiff Φ1).comp (fstCLM N1 N2).contDiff
  have h2 : ContDiff ℝ ∞ (fun x : X (N1+N2) =>
      (shifted N2 (L - L2) (Φ2 : X N2 → ℝ)) (lastBlock N1 N2 x)) :=
    (shifted_contDiff (psi_contDiff Φ2)).comp (lstCLM N1 N2).contDiff
  exact ContDiff.mul h1 h2

lemma mem_box_split (N1 N2 : ℕ) (L : ℝ) (x : X (N1+N2)) :
    x ∈ box (N1+N2) L ↔ firstBlock N1 N2 x ∈ box N1 L ∧ lastBlock N1 N2 x ∈ box N2 L := by
  rw [mem_box_iff, mem_box_iff, mem_box_iff]
  constructor
  · intro h
    constructor
    · intro i k; exact h (Fin.castAdd N2 i) k
    · intro j k; exact h (Fin.natAdd N1 j) k
  · intro h k kk
    by_cases hk : k.val < N1
    · let i : Fin N1 := ⟨k.val, hk⟩
      have hkeq : k = Fin.castAdd N2 i := by ext; simp [i]
      rw [hkeq]; exact h.1 i kk
    · let j : Fin N2 := ⟨k.val - N1, by omega⟩
      have hkeq : k = Fin.natAdd N1 j := by ext; simp [j]; omega
      rw [hkeq]; exact h.2 j kk

/-- support of the shifted state sits above the support of the unshifted one -/
lemma shifted_support_preimage {N : ℕ} {d : ℝ} {f : X N → ℝ} :
    Function.support (shifted N d f) ⊆ (addShift N d) ⁻¹' Function.support f := by
  intro w hw
  change f (addShift N d w) ≠ 0
  by_contra h2
  apply hw
  simp [shifted, h2]

/-- tsupport of the trial state is inside the two open corner-boxes. -/
lemma tsupport_trial_subset {N1 N2 : ℕ} {L L1 L2 : ℝ} (Φ1 : CInfty0Box N1 L1)
    (Φ2 : CInfty0Box N2 L2) :
    tsupport (trialFun N1 N2 (L := L) (L1 := L1) (L2 := L2) Φ1 Φ2) ⊆
      (firstBlock N1 N2 ⁻¹' interior (box N1 L1)) ∩
        (lastBlock N1 N2 ⁻¹' ((addShift N2 (L - L2)) ⁻¹' interior (box N2 L2))) := by
  let f1 : X N1 → ℝ := (Φ1 : X N1 → ℝ)
  let f2 : X N2 → ℝ := shifted N2 (L - L2) (Φ2 : X N2 → ℝ)
  have hsupp : Function.support (trialFun N1 N2 (L := L) (L1 := L1) (L2 := L2) Φ1 Φ2) ⊆
      (firstBlock N1 N2 ⁻¹' Function.support f1) ∩
        (lastBlock N1 N2 ⁻¹' Function.support f2) := by
    intro x hx
    constructor
    · change f1 (firstBlock N1 N2 x) ≠ 0
      by_contra hz
      apply hx
      have h : f1 (firstBlock N1 N2 x) * f2 (lastBlock N1 N2 x) = 0 := by
        rw [hz, zero_mul]
      simpa [trialFun, prodState, f1, f2] using h
    · change f2 (lastBlock N1 N2 x) ≠ 0
      by_contra hz
      apply hx
      have h : f1 (firstBlock N1 N2 x) * f2 (lastBlock N1 N2 x) = 0 := by
        rw [hz, mul_zero]
      simpa [trialFun, prodState, f1, f2] using h
  have hf1c : closure (Function.support f1) ⊆ interior (box N1 L1) := by
    simpa [f1, tsupport] using Φ1.support
  have hcl1 : closure (firstBlock N1 N2 ⁻¹' Function.support f1) ⊆
      firstBlock N1 N2 ⁻¹' (closure (Function.support f1)) :=
    (firstBlock_continuous N1 N2).closure_preimage_subset (Function.support f1)
  have hpre2 : Function.support f2 ⊆
      (addShift N2 (L - L2)) ⁻¹' Function.support (Φ2 : X N2 → ℝ) := by
    simpa [f2] using (shifted_support_preimage (N := N2) (d := L - L2) (f := (Φ2 : X N2 → ℝ)))
  have hcl2a : closure (Function.support f2) ⊆
      (addShift N2 (L - L2)) ⁻¹' interior (box N2 L2) := by
    calc
      closure (Function.support f2)
          ⊆ closure ((addShift N2 (L - L2)) ⁻¹' Function.support (Φ2 : X N2 → ℝ)) := closure_mono hpre2
      _ ⊆ (addShift N2 (L - L2)) ⁻¹' (closure (Function.support (Φ2 : X N2 → ℝ))) :=
            (addShift_continuous N2 (L - L2)).closure_preimage_subset _
      _ ⊆ (addShift N2 (L - L2)) ⁻¹' interior (box N2 L2) := by
            exact Set.preimage_mono Φ2.support
  have hcl2b : closure (lastBlock N1 N2 ⁻¹' Function.support f2) ⊆
      lastBlock N1 N2 ⁻¹' (closure (Function.support f2)) :=
    (lastBlock_continuous N1 N2).closure_preimage_subset (Function.support f2)
  calc
    closure (Function.support (trialFun N1 N2 (L := L) (L1 := L1) (L2 := L2) Φ1 Φ2))
        ⊆ closure ((firstBlock N1 N2 ⁻¹' Function.support f1) ∩
            (lastBlock N1 N2 ⁻¹' Function.support f2)) := closure_mono hsupp
    _ ⊆ closure (firstBlock N1 N2 ⁻¹' Function.support f1) ∩
          closure (lastBlock N1 N2 ⁻¹' Function.support f2) := closure_inter_subset
    _ ⊆ (firstBlock N1 N2 ⁻¹' (closure (Function.support f1))) ∩
          (lastBlock N1 N2 ⁻¹' (closure (Function.support f2))) := by
          exact Set.inter_subset_inter hcl1 hcl2b
    _ ⊆ (firstBlock N1 N2 ⁻¹' interior (box N1 L1)) ∩
          (lastBlock N1 N2 ⁻¹' ((addShift N2 (L - L2)) ⁻¹' interior (box N2 L2))) := by
          exact Set.inter_subset_inter (Set.preimage_mono hf1c)
            (Set.preimage_mono hcl2a)

/-- the two corner-boxes lie inside the big box -/
lemma corner_subset_box3 {N1 N2 : ℕ} {L L1 L2 : ℝ} (hL1L : L1 ≤ L) (hD : 0 ≤ L - L2)
    (x : X (N1+N2)) :
    x ∈ (firstBlock N1 N2 ⁻¹' interior (box N1 L1)) ∩
        (lastBlock N1 N2 ⁻¹' ((addShift N2 (L - L2)) ⁻¹' interior (box N2 L2))) →
      x ∈ box (N1+N2) L := by
  intro hx
  rw [mem_box_split]
  constructor
  · have h1 : firstBlock N1 N2 x ∈ interior (box N1 L1) := hx.1
    have h2 : firstBlock N1 N2 x ∈ box N1 L1 := interior_subset h1
    exact box_mono hL1L h2
  · have h2 : (addShift N2 (L - L2)) (lastBlock N1 N2 x) ∈ interior (box N2 L2) := hx.2
    have h3 : (addShift N2 (L - L2)) (lastBlock N1 N2 x) ∈ box N2 L2 := interior_subset h2
    rw [mem_box_iff]
    intro j k
    have hjk : ((addShift N2 (L - L2)) (lastBlock N1 N2 x) j).ofLp k ∈ Set.Icc 0 L2 := by
      simpa using h3 j k
    let c : ℝ := (lastBlock N1 N2 x j).ofLp k
    have hd : ((addShift N2 (L - L2)) (lastBlock N1 N2 x) j).ofLp k = c - (L - L2) := by
      simp [addShift, offVec, c, sub_eq_add_neg]
    have hjk' : c - (L - L2) ∈ Set.Icc 0 L2 := by
      rwa [hd] at hjk
    have hlo : 0 ≤ c := by linarith [hjk'.1, hD]
    have hhi : c ≤ L := by linarith [hjk'.2]
    change 0 ≤ c ∧ c ≤ L
    exact ⟨hlo, hhi⟩

/-- the two corner-boxes form an open set -/
lemma corner_open {N1 N2 : ℕ} {L L1 L2 : ℝ} :
    IsOpen ((firstBlock N1 N2 ⁻¹' interior (box N1 L1)) ∩
        (lastBlock N1 N2 ⁻¹' ((addShift N2 (L - L2)) ⁻¹' interior (box N2 L2)))) := by
  refine IsOpen.inter ?_ ?_
  · exact IsOpen.preimage (firstBlock_continuous N1 N2) isOpen_interior
  · exact IsOpen.preimage (lastBlock_continuous N1 N2)
      (IsOpen.preimage (addShift_continuous N2 (L - L2)) isOpen_interior)

/-- tsupport of the trial state is inside the interior of the big box -/
lemma trial_support_interior {N1 N2 : ℕ} {L L1 L2 : ℝ} (hL1L : L1 ≤ L) (hD : 0 ≤ L - L2)
    (Φ1 : CInfty0Box N1 L1) (Φ2 : CInfty0Box N2 L2) :
    tsupport (trialFun N1 N2 (L := L) (L1 := L1) (L2 := L2) Φ1 Φ2) ⊆
      interior (box (N1+N2) L) := by
  let O : Set (X (N1+N2)) := (firstBlock N1 N2 ⁻¹' interior (box N1 L1)) ∩
      (lastBlock N1 N2 ⁻¹' ((addShift N2 (L - L2)) ⁻¹' interior (box N2 L2)))
  have h1 : tsupport (trialFun N1 N2 (L := L) (L1 := L1) (L2 := L2) Φ1 Φ2) ⊆ O := by
    simpa [O] using (tsupport_trial_subset (L := L) (L1 := L1) (L2 := L2) Φ1 Φ2)
  have h2 : O ⊆ interior (box (N1+N2) L) := interior_maximal
    (by intro x hx; exact corner_subset_box3 hL1L hD x hx)
    (corner_open (N1 := N1) (N2 := N2) (L := L) (L1 := L1) (L2 := L2))
  exact h1.trans h2

/-! The support of a state is contained in the closed box. -/
lemma support_subset_box_state {N : ℕ} {L : ℝ} (Φ : CInfty0Box N L) :
    Function.support (Φ : X N → ℝ) ⊆ box N L := by
  intro x hx
  exact psi_support_box Φ hx

/-! ## Pointwise kinetic and interaction functions -/

/-- The full two-body sum `Σ_{i<j} v (x_i - x_j)`. -/
def pairSum (N : ℕ) (v : ℝ³ → ℝ) (x : X N) : ℝ :=
  ∑ p ∈ (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)), v (x p.1 - x p.2)

/-- The cross pair sum `Σ_{i,j} v (u_i - w_j)` between the two blocks. -/
def crossSum (N1 N2 : ℕ) (v : ℝ³ → ℝ) (u : X N1) (w : X N2) : ℝ :=
  ∑ i : Fin N1, ∑ j : Fin N2, v (u i - w j)

/-- The pointwise kinetic integrand `Σ_i f x · (-Δ_i f x)`. -/
noncomputable def kinP (N : ℕ) (f : X N → ℝ) : X N → ℝ :=
  fun x => ∑ i : Fin N, f x * (-(partialLaplacian i f x))


/-! ## Product-box change of variables -/

lemma preimage_box (N1 N2 : ℕ) (L : ℝ) :
    (blockSplitEquiv N1 N2) ⁻¹' ((box N1 L) ×ˢ (box N2 L)) = box (N1+N2) L := by
  ext x
  simp [blockSplitEquiv_apply, mem_box_split]

lemma vol_prod_restrict (N1 N2 : ℕ) (L : ℝ) :
    ((volume.restrict (box N1 L)).prod (volume.restrict (box N2 L))) =
      ((volume : Measure (X N1 × X N2)).restrict ((box N1 L) ×ˢ (box N2 L))) := by
  rw [Measure.prod_restrict]
  rfl

lemma blockSplit_measurePreserving_restrict (N1 N2 : ℕ) (L : ℝ) :
    MeasurePreserving (blockSplitEquiv N1 N2)
      (volume.restrict (box (N1+N2) L))
      ((volume.restrict (box N1 L)).prod (volume.restrict (box N2 L))) := by
  have hmp : MeasurePreserving (blockSplitEquiv N1 N2)
      (volume : Measure (X (N1+N2))) (volume : Measure (X N1 × X N2)) := blockSplitEquiv_measurePreserving N1 N2
  have hres := hmp.restrict_preimage_emb (blockSplitEquiv N1 N2).measurableEmbedding
    ((box N1 L) ×ˢ (box N2 L))
  simpa [preimage_box, vol_prod_restrict] using hres

/-- A product integral over the big box factorises over the two blocks
(no integrability hypotheses). -/
lemma boxIntegral_prod_fun {N1 N2 : ℕ} (L : ℝ) (a : X N1 → ℝ) (b : X N2 → ℝ) :
    (∫ x in box (N1+N2) L, a (firstBlock N1 N2 x) * b (lastBlock N1 N2 x)) =
      (∫ u in box N1 L, a u) * (∫ w in box N2 L, b w) := by
  have hc := (blockSplit_measurePreserving_restrict N1 N2 L).integral_comp
    (blockSplitEquiv N1 N2).measurableEmbedding (fun p : X N1 × X N2 => a p.1 * b p.2)
  calc
    (∫ x in box (N1+N2) L, a (firstBlock N1 N2 x) * b (lastBlock N1 N2 x))
        = ∫ x : X (N1+N2), (fun p : X N1 × X N2 => a p.1 * b p.2)
            (blockSplitEquiv N1 N2 x) ∂(volume.restrict (box (N1+N2) L)) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [blockSplitEquiv_apply]
    _ = ∫ p : X N1 × X N2, a p.1 * b p.2
          ∂((volume.restrict (box N1 L)).prod (volume.restrict (box N2 L))) := hc
    _ = (∫ u in box N1 L, a u) * (∫ w in box N2 L, b w) := by
          rw [MeasureTheory.integral_prod_mul (μ := volume.restrict (box N1 L))
            (ν := volume.restrict (box N2 L))]

/-- Integrability of a product of functions over the two boxes lifts to the product box. -/
lemma integrableOn_prod_box {N1 N2 : ℕ} (L : ℝ) {a : X N1 → ℝ} {b : X N2 → ℝ}
    (ha : IntegrableOn a (box N1 L) volume) (hb : IntegrableOn b (box N2 L) volume) :
    IntegrableOn (fun x : X (N1+N2) => a (firstBlock N1 N2 x) * b (lastBlock N1 N2 x))
      (box (N1+N2) L) volume := by
  have hres := blockSplit_measurePreserving_restrict N1 N2 L
  have hf : Integrable (fun p : X N1 × X N2 => a p.1 * b p.2)
      ((volume.restrict (box N1 L)).prod (volume.restrict (box N2 L))) := by
    exact Integrable.mul_prod ha hb
  -- transport integrability across the measure-preserving measurable embedding
  have hif : Integrable (fun x : X (N1+N2) =>
        (fun p : X N1 × X N2 => a p.1 * b p.2) (blockSplitEquiv N1 N2 x))
      (volume.restrict (box (N1+N2) L)) := by
    exact (hres.integrable_comp_emb (blockSplitEquiv N1 N2).measurableEmbedding
      (g := fun p : X N1 × X N2 => a p.1 * b p.2)).mpr hf
  change Integrable (fun x : X (N1+N2) =>
        a (firstBlock N1 N2 x) * b (lastBlock N1 N2 x)) (volume.restrict (box (N1+N2) L))
  simpa [blockSplitEquiv_apply] using hif

/-! ## Pair-sum splitting and vanishing of the cross terms -/

/-- Coordinates after the shift: `(w j) k ∈ [d, d + L2]`. -/
lemma coord_addShift_apply {d L2 : ℝ} {w : ℝ³} (k : Fin 3)
    (hw : (w - offVec d).ofLp k ∈ Set.Icc 0 L2) : w.ofLp k ∈ Set.Icc d (d + L2) := by
  let c : ℝ := w.ofLp k
  have hw' : c - d ∈ Set.Icc 0 L2 := by
    simpa [c, offVec] using hw
  have hlo : d ≤ c := by linarith [hw'.1]
  have hhi : c ≤ d + L2 := by linarith [hw'.2]
  exact ⟨by simpa [c] using hlo, by simpa [c] using hhi⟩

/-- A point of the first block and a point of the far-corner block have separation ≥ R. -/
lemma v_zero_cross_coords {N1 N2 : ℕ} {L L1 L2 R : ℝ} {v : ℝ³ → ℝ}
    (hR : 0 ≤ R) (hsep : L1 + L2 + R ≤ L)
    (hsupp : tsupport v ⊆ ball (0 : ℝ³) R)
    {u : X N1} {w : X N2} (hu : u ∈ box N1 L1)
    (hw : (addShift N2 (L - L2)) w ∈ box N2 L2)
    (i : Fin N1) (j : Fin N2) : v (u i - w j) = 0 := by
  have hu' : ∀ k : Fin 3, ((u i) k) ∈ Set.Icc 0 L1 := by
    have := ((mem_box_iff N1 L1 u).mp hu) i
    simpa using this
  have hw' : ∀ k : Fin 3, ((w j) k) ∈ Set.Icc (L - L2) L := by
    intro k
    have hwj := ((mem_box_iff N2 L2 ((addShift N2 (L - L2)) w)).mp hw) j
    let c : ℝ := (w j).ofLp k
    have hc : c - (L - L2) ∈ Set.Icc 0 L2 := by
      simpa [c, addShift, offVec, sub_eq_add_neg] using hwj k
    constructor <;> linarith [hc.1, hc.2]
  have hdist : R ≤ ‖(w j) - (u i)‖ := dist_ge_of_cubes hR hsep hu' hw'
  have hnorm : R ≤ ‖(u i) - (w j)‖ := by
    simpa [norm_sub_rev] using hdist
  exact v_eq_zero_of_norm_ge hsupp hnorm

/-- The cross pair sum vanishes on the support of the trial state. -/
lemma trial_crossSum_zero {N1 N2 : ℕ} {L L1 L2 R : ℝ} {v : ℝ³ → ℝ}
    (hR : 0 ≤ R) (hsep : L1 + L2 + R ≤ L)
    (hsupp : tsupport v ⊆ ball (0 : ℝ³) R)
    (Φ1 : CInfty0Box N1 L1) (Φ2 : CInfty0Box N2 L2) (x : X (N1+N2)) :
    (trialFun N1 N2 (L := L) (L1 := L1) (L2 := L2) Φ1 Φ2 x) ^ 2 *
        crossSum N1 N2 v (firstBlock N1 N2 x) (lastBlock N1 N2 x) = 0 := by
  let f1 : X N1 → ℝ := (Φ1 : X N1 → ℝ)
  let f2 : X N2 → ℝ := shifted N2 (L - L2) (Φ2 : X N2 → ℝ)
  by_cases hx : trialFun N1 N2 (L := L) (L1 := L1) (L2 := L2) Φ1 Φ2 x = 0
  · simp [hx]
  · have hf1 : f1 (firstBlock N1 N2 x) ≠ 0 := by
      intro h
      apply hx
      have hh : f1 (firstBlock N1 N2 x) * f2 (lastBlock N1 N2 x) = 0 := by
        rw [h, zero_mul]
      simpa [trialFun, prodState, f1, f2] using hh
    have hf2 : f2 (lastBlock N1 N2 x) ≠ 0 := by
      intro h
      apply hx
      have hh : f1 (firstBlock N1 N2 x) * f2 (lastBlock N1 N2 x) = 0 := by
        rw [h, mul_zero]
      simpa [trialFun, prodState, f1, f2] using hh
    let u : X N1 := firstBlock N1 N2 x
    let w : X N2 := lastBlock N1 N2 x
    have hu : u ∈ box N1 L1 := by
      exact support_subset_box_state Φ1 (by simpa [f1, u] using hf1)
    have hw : (addShift N2 (L - L2)) w ∈ box N2 L2 := by
      exact support_subset_box_state Φ2 (by
        simpa [f2, w, shifted] using (shifted_support_preimage (N := N2) (d := L - L2)
          (f := (Φ2 : X N2 → ℝ)) (by simpa [f2, w] using hf2)))
    have hz : ∀ i : Fin N1, ∀ j : Fin N2, v (u i - w j) = 0 := by
      intro i j
      exact v_zero_cross_coords (N1 := N1) (N2 := N2) hR hsep hsupp hu hw i j
    calc
      (trialFun N1 N2 (L := L) (L1 := L1) (L2 := L2) Φ1 Φ2 x) ^ 2 *
            crossSum N1 N2 v u w
          = (f1 u * f2 w) ^ 2 * crossSum N1 N2 v u w := by
            simp [trialFun, prodState, u, w, f1, f2]
      _ = 0 := by
            have hfprod : f1 u ≠ 0 ∧ f2 w ≠ 0 := ⟨by simpa [u] using hf1, by simpa [w] using hf2⟩
            simp [crossSum, hz]

/-- The pair sum over `Fin (N1+N2)` splits into the two blocks and the cross terms. -/
lemma pairSum_block_split (N1 N2 : ℕ) (v : ℝ³ → ℝ) (x : X (N1+N2)) :
    pairSum (N1+N2) v x = pairSum N1 v (firstBlock N1 N2 x) + pairSum N2 v (lastBlock N1 N2 x)
      + crossSum N1 N2 v (firstBlock N1 N2 x) (lastBlock N1 N2 x) := by
  have hch := sum_pairs_block_split (M := ℝ) (g := fun a b => v (x a - x b))
  simpa [pairSum, crossSum, firstBlock, lastBlock] using hch

/-- Pointwise: the cross terms of the trial state vanish. -/
lemma trial_int_pointwise {N1 N2 : ℕ} {L L1 L2 R : ℝ} {v : ℝ³ → ℝ}
    (hR : 0 ≤ R) (hsep : L1 + L2 + R ≤ L)
    (hsupp : tsupport v ⊆ ball (0 : ℝ³) R)
    (Φ1 : CInfty0Box N1 L1) (Φ2 : CInfty0Box N2 L2) (x : X (N1+N2)) :
    (trialFun N1 N2 (L := L) (L1 := L1) (L2 := L2) Φ1 Φ2 x)^2 * pairSum (N1+N2) v x =
      (trialFun N1 N2 (L := L) (L1 := L1) (L2 := L2) Φ1 Φ2 x)^2 *
        (pairSum N1 v (firstBlock N1 N2 x) + pairSum N2 v (lastBlock N1 N2 x)) := by
  have hz := trial_crossSum_zero (N1 := N1) (N2 := N2) (L := L) (L1 := L1) (L2 := L2)
    (R := R) hR hsep hsupp Φ1 Φ2 x
  calc
    (trialFun N1 N2 (L := L) (L1 := L1) (L2 := L2) Φ1 Φ2 x)^2 * pairSum (N1+N2) v x
        = (trialFun N1 N2 (L := L) (L1 := L1) (L2 := L2) Φ1 Φ2 x)^2 *
            (pairSum N1 v (firstBlock N1 N2 x) + pairSum N2 v (lastBlock N1 N2 x) +
              crossSum N1 N2 v (firstBlock N1 N2 x) (lastBlock N1 N2 x)) := by
          rw [pairSum_block_split]
    _ = (trialFun N1 N2 (L := L) (L1 := L1) (L2 := L2) Φ1 Φ2 x)^2 *
            (pairSum N1 v (firstBlock N1 N2 x) + pairSum N2 v (lastBlock N1 N2 x)) := by
          nlinarith [hz]

/-- Pointwise kinetic identity for the product state. -/
lemma kinP_pointwise {N1 N2 : ℕ} {f1 : X N1 → ℝ} {f2 : X N2 → ℝ}
    (h1 : ContDiff ℝ 2 f1) (h2 : ContDiff ℝ 2 f2) (x : X (N1+N2)) :
    kinP (N1+N2) (prodState N1 N2 f1 f2) x =
      kinP N1 f1 (firstBlock N1 N2 x) * (f2 (lastBlock N1 N2 x))^2 +
      (f1 (firstBlock N1 N2 x))^2 * kinP N2 f2 (lastBlock N1 N2 x) := by
  let u : X N1 := firstBlock N1 N2 x
  let v : X N2 := lastBlock N1 N2 x
  have h1t : ∀ i1 : Fin N1,
      (prodState N1 N2 f1 f2 x) * (-(partialLaplacian (Fin.castAdd N2 i1) (prodState N1 N2 f1 f2) x)) =
        (f1 u * (-(partialLaplacian i1 f1 u))) * (f2 v)^2 := by
    intro i1
    rw [partialLaplacian_prodState_first (f1 := f1) (f2 := f2) h1 i1 x]
    simp [prodState, u, v]
    ring
  have h2t : ∀ j2 : Fin N2,
      (prodState N1 N2 f1 f2 x) * (-(partialLaplacian (Fin.natAdd N1 j2) (prodState N1 N2 f1 f2) x)) =
        (f1 u)^2 * (f2 v * (-(partialLaplacian j2 f2 v))) := by
    intro j2
    rw [partialLaplacian_prodState_last (f1 := f1) (f2 := f2) h2 j2 x]
    simp [prodState, u, v]
    ring
  have hsum1 : (∑ i1 : Fin N1,
      (prodState N1 N2 f1 f2 x) * (-(partialLaplacian (Fin.castAdd N2 i1) (prodState N1 N2 f1 f2) x))) =
      (∑ i1 : Fin N1, f1 u * (-(partialLaplacian i1 f1 u))) * (f2 v)^2 := by
    calc
      (∑ i1 : Fin N1,
          (prodState N1 N2 f1 f2 x) * (-(partialLaplacian (Fin.castAdd N2 i1) (prodState N1 N2 f1 f2) x)))
          = ∑ i1 : Fin N1, (f1 u * (-(partialLaplacian i1 f1 u))) * (f2 v)^2 := by
            apply Finset.sum_congr rfl
            intro i1 hi1
            exact h1t i1
      _ = (∑ i1 : Fin N1, f1 u * (-(partialLaplacian i1 f1 u))) * (f2 v)^2 := by
            rw [Finset.sum_mul]
  have hsum2 : (∑ j2 : Fin N2,
      (prodState N1 N2 f1 f2 x) * (-(partialLaplacian (Fin.natAdd N1 j2) (prodState N1 N2 f1 f2) x))) =
      (f1 u)^2 * (∑ j2 : Fin N2, f2 v * (-(partialLaplacian j2 f2 v))) := by
    calc
      (∑ j2 : Fin N2,
          (prodState N1 N2 f1 f2 x) * (-(partialLaplacian (Fin.natAdd N1 j2) (prodState N1 N2 f1 f2) x)))
          = ∑ j2 : Fin N2, (f1 u)^2 * (f2 v * (-(partialLaplacian j2 f2 v))) := by
            apply Finset.sum_congr rfl
            intro j2 hj2
            exact h2t j2
      _ = (f1 u)^2 * (∑ j2 : Fin N2, f2 v * (-(partialLaplacian j2 f2 v))) := by
            rw [Finset.mul_sum]
  unfold kinP
  rw [Fin.sum_univ_add]
  rw [hsum1, hsum2]

/-! ## Whole-space equality of box integrals for states -/

/-- An integral over the box of a state equals the whole-space integral when the
integrand vanishes with the state. -/
lemma box_eq_whole_of_state {N : ℕ} {L : ℝ} (Φ : CInfty0Box N L) {f : X N → ℝ}
    (hf : ∀ x, (Φ : X N → ℝ) x = 0 → f x = 0) :
    (∫ x in box N L, f x) = ∫ x : X N, f x :=
  setIntegral_eq_integral_of_forall_compl_eq_zero (by
    intro x hx
    exact hf x (psi_eq_zero_of_not_mem_box Φ hx))

/-! ## Translation as a measurable equivalence -/

/-- Translation by adding a fixed configuration is a measurable equivalence. -/
noncomputable def translateEquiv {N : ℕ} (c : X N) : X N ≃ᵐ X N where
  toEquiv :=
    { toFun := fun x => x + c
      invFun := fun x => x - c
      left_inv := by intro x; ext i; simp
      right_inv := by intro x; ext i; simp }
  measurable_toFun := by
    have hc : Continuous (fun x : X N => x + c) := continuous_id.add continuous_const
    exact hc.measurable
  measurable_invFun := by
    have hc : Continuous (fun x : X N => x - c) := continuous_id.sub continuous_const
    exact hc.measurable

@[simp] lemma translateEquiv_coe {N : ℕ} (c : X N) : ⇑(translateEquiv c) = fun x : X N => x + c := by
  funext x
  rfl

/-- Translations preserve Lebesgue measure. -/
lemma translateEquiv_measurePreserving {N : ℕ} (c : X N) : MeasurePreserving (fun x : X N => x + c) := by
  have h : MeasurePreserving (translateEquiv c) := by
    simpa [translateEquiv] using (measurePreserving_add_right (μ := (volume : Measure (X N))) c)
  simpa using h

/-- `addShift N d` is translation by `(-offVec d)` in every particle. -/
lemma addShift_eq_translate (N : ℕ) (d : ℝ) :
    addShift N d = fun w : X N => w + (fun _ : Fin N => -offVec d) := by
  funext w
  rfl

lemma addShift_measurePreserving' (N : ℕ) (d : ℝ) : MeasurePreserving (addShift N d) := by
  change MeasurePreserving (fun w : X N => w + (fun _ : Fin N => -offVec d))
  exact measurePreserving_add_right (μ := (volume : Measure (X N))) (-(fun _ : Fin N => offVec d))

lemma addShift_measurableEmbedding (N : ℕ) (d : ℝ) : MeasurableEmbedding (addShift N d) := by
  change MeasurableEmbedding (fun w : X N => w + (fun _ : Fin N => -offVec d))
  simpa [translateEquiv_coe] using
    (translateEquiv (N := N) (fun _ : Fin N => -offVec d)).measurableEmbedding

/-- `pairSum` is invariant under the global shift (relative coordinates). -/
lemma pairSum_addShift {N : ℕ} (v : ℝ³ → ℝ) (d : ℝ) (w : X N) :
    pairSum N v (addShift N d w) = pairSum N v w := by
  unfold pairSum
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  ext k
  simp [addShift, offVec]

/-- The interaction integrand of a shifted state is the pullback of the original one. -/
lemma intP_shifted {N : ℕ} (v : ℝ³ → ℝ) (d : ℝ) (f : X N → ℝ) (w : X N) :
    (shifted N d f w)^2 * pairSum N v w = (fun z : X N => (f z)^2 * pairSum N v z) (addShift N d w) := by
  simp [shifted, pairSum_addShift]

/-! ## Integrability of the `Φ²·pairSum` functions -/

/-- `(Φ x)² · pairSum N v x` is integrable over the box of the state. -/
lemma integrableOn_state_int {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L) (hv1 : MemLp v 1)
    (Φ : CInfty0Box N L) :
    IntegrableOn (fun x : X N => ((Φ : X N → ℝ) x)^2 * pairSum N v x) (box N L) volume := by
  exact integrableOn_intIntegrand hL hv1 Φ

/-- Its support is contained in the box of the state. -/
lemma support_int_of_state {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (Φ : CInfty0Box N L) :
    Function.support (fun x : X N => ((Φ : X N → ℝ) x)^2 * pairSum N v x) ⊆ box N L := by
  intro x hx
  exact support_subset_box_state Φ (by
    intro hz
    apply hx
    simp [hz])

/-- Whole-space integrability. -/
lemma integrable_whole_int_of_state {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L) (hv1 : MemLp v 1)
    (Φ : CInfty0Box N L) :
    Integrable (fun x : X N => ((Φ : X N → ℝ) x)^2 * pairSum N v x) volume := by
  exact (integrableOn_iff_integrable_of_support_subset (support_int_of_state Φ)).mp
    (integrableOn_state_int hL hv1 Φ)

/-- The same over a bigger box. -/
lemma integrableOn_state_int_big {N : ℕ} {L L' : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L) (hLL' : L ≤ L')
    (hv1 : MemLp v 1) (Φ : CInfty0Box N L) :
    IntegrableOn (fun x : X N => ((Φ : X N → ℝ) x)^2 * pairSum N v x) (box N L') volume := by
  have hw := integrable_whole_int_of_state hL hv1 Φ
  exact hw.mono_measure Measure.restrict_le_self

/-- The interaction integrand of a translated state is integrable over the big box. -/
lemma integrableOn_int_shifted_big {N : ℕ} {L2 d : ℝ} {v : ℝ³ → ℝ} (hL2 : 0 < L2)
    (hv1 : MemLp v 1) (Φ2 : CInfty0Box N L2) :
    IntegrableOn (fun w : X N => (shifted N d (Φ2 : X N → ℝ) w)^2 * pairSum N v w)
      (box N (d + L2)) volume := by
  have hpt : (fun w : X N => (shifted N d (Φ2 : X N → ℝ) w)^2 * pairSum N v w) =
      (fun z : X N => ((Φ2 : X N → ℝ) z)^2 * pairSum N v z) ∘ (addShift N d) := by
    funext w
    simpa [intP_shifted, Function.comp_def] using (intP_shifted v d (Φ2 : X N → ℝ) w)
  have hw : Integrable (fun w : X N => (shifted N d (Φ2 : X N → ℝ) w)^2 * pairSum N v w) volume := by
    have hg : Integrable (fun z : X N => ((Φ2 : X N → ℝ) z)^2 * pairSum N v z) volume :=
      integrable_whole_int_of_state hL2 hv1 Φ2
    have hmp : MeasurePreserving (addShift N d) := addShift_measurePreserving' N d
    have hp : Integrable (fun w : X N =>
        ((Φ2 : X N → ℝ) (addShift N d w))^2 * pairSum N v (addShift N d w)) volume :=
      (hmp.integrable_comp_emb (addShift_measurableEmbedding N d)
        (g := fun z : X N => ((Φ2 : X N → ℝ) z)^2 * pairSum N v z)).mpr hg
    simpa [hpt, Function.comp_def] using hp
  exact hw.mono_measure Measure.restrict_le_self

/-! ## Rayleigh quotient and the trial state -/

/-- The Rayleigh quotient function whose infimum is `boxEnergy`. -/
noncomputable def boxQuot (N : ℕ) (L : ℝ) (v : ℝ³ → ℝ) (Φ : CInfty0Box N L) : ℝ :=
  (∫ x in box N L, (Φ : X N → ℝ) x * _root_.BoseGases.𝓗 N v (Φ : X N → ℝ) x) /
    (√ (∫ x in box N L, (Φ : X N → ℝ) x * (Φ : X N → ℝ) x)) ^ 2

lemma boxEnergy_eq_ciInf_boxQuot (N : ℕ) (L : ℝ) (v : ℝ³ → ℝ) :
    boxEnergy N L v = ⨅ Φ : CInfty0Box N L, boxQuot N L v Φ := by
  unfold boxEnergy boxQuot
  rfl

/-- The trial state is nonzero. -/
lemma trial_nezero {N1 N2 : ℕ} {L L1 L2 : ℝ} (Φ1 : CInfty0Box N1 L1) (Φ2 : CInfty0Box N2 L2) :
    trialFun N1 N2 (L := L) (L1 := L1) (L2 := L2) Φ1 Φ2 ≠ 0 := by
  intro hzero
  have h1 : ∃ u0 : X N1, (Φ1 : X N1 → ℝ) u0 ≠ 0 := by
    by_contra h
    have hz : (Φ1 : X N1 → ℝ) = 0 := by
      funext u
      by_contra hu
      exact h ⟨u, hu⟩
    exact Φ1.nezero hz
  have h2 : ∃ w0 : X N2, (Φ2 : X N2 → ℝ) w0 ≠ 0 := by
    by_contra h
    have hz : (Φ2 : X N2 → ℝ) = 0 := by
      funext w
      by_contra hw
      exact h ⟨w, hw⟩
    exact Φ2.nezero hz
  rcases h1 with ⟨u0, hu0⟩
  rcases h2 with ⟨w0, hw0⟩
  let x0 : X (N1+N2) := mergeBlock N1 N2 (u0, w0 - (fun _ : Fin N2 => -offVec (L - L2)))
  have hfirst : firstBlock N1 N2 x0 = u0 := by simp [x0, mergeBlock_first]
  have hlast : (addShift N2 (L - L2)) (lastBlock N1 N2 x0) = w0 := by
    simp [x0, addShift, lastBlock, mergeBlock_last]
  have hφ2 : shifted N2 (L - L2) (Φ2 : X N2 → ℝ) (lastBlock N1 N2 x0) ≠ 0 := by
    intro hz
    apply hw0
    simpa [shifted, hlast] using hz
  have hval : trialFun N1 N2 (L := L) (L1 := L1) (L2 := L2) Φ1 Φ2 x0 ≠ 0 := by
    intro hz
    have hpt : (Φ1 : X N1 → ℝ) (firstBlock N1 N2 x0) *
        shifted N2 (L - L2) (Φ2 : X N2 → ℝ) (lastBlock N1 N2 x0) = 0 := by
      simpa [trialFun, prodState] using hz
    rcases mul_eq_zero.mp hpt with hL | hR
    · exact hu0 (by simpa [hfirst] using hL)
    · exact hφ2 (by simpa using hR)
  exact hval (congrFun hzero x0)

/-- The trial state as an element of `CInfty0Box (N1+N2) L`. -/
noncomputable def trialState (N1 N2 : ℕ) {L L1 L2 : ℝ} (hL1 : 0 < L1) (hL2 : 0 < L2)
    {R : ℝ} (hR : 0 ≤ R) (hL : L1 + L2 + R ≤ L)
    (Φ1 : CInfty0Box N1 L1) (Φ2 : CInfty0Box N2 L2) : CInfty0Box (N1+N2) L := by
  refine ⟨trialFun N1 N2 (L := L) (L1 := L1) (L2 := L2) Φ1 Φ2, ?_, ?_, ?_⟩
  · -- ContDiffOn on the box
    have hL1L : L1 ≤ L := by linarith
    have hD : 0 ≤ L - L2 := by linarith
    exact (contDiff_trialFun Φ1 Φ2).contDiffOn
  · -- support
    have hL1L : L1 ≤ L := by linarith
    have hD : 0 ≤ L - L2 := by linarith
    exact trial_support_interior hL1L hD Φ1 Φ2
  · -- nonzero
    exact trial_nezero Φ1 Φ2

lemma trialState_eq {N1 N2 : ℕ} {L L1 L2 : ℝ} (hL1 : 0 < L1) (hL2 : 0 < L2)
    {R : ℝ} (hR : 0 ≤ R) (hL : L1 + L2 + R ≤ L)
    (Φ1 : CInfty0Box N1 L1) (Φ2 : CInfty0Box N2 L2) :
    ((trialState N1 N2 hL1 hL2 hR hL Φ1 Φ2 : CInfty0Box (N1+N2) L) : X (N1+N2) → ℝ) =
      trialFun N1 N2 (L := L) (L1 := L1) (L2 := L2) Φ1 Φ2 := by
  rfl

/-! ## Kinetic energy of the product state -/

/-- A first-block kinetic term of the product state factorises. -/
lemma kinetic_term_first {N1 N2 : ℕ} {L : ℝ} {f1 : X N1 → ℝ} {f2 : X N2 → ℝ}
    (h1 : ContDiff ℝ 2 f1) (i1 : Fin N1) :
    (∫ x in box (N1+N2) L,
        (prodState N1 N2 f1 f2 x) * (-(partialLaplacian (Fin.castAdd N2 i1) (prodState N1 N2 f1 f2) x))) =
      (∫ u in box N1 L, f1 u * (-(partialLaplacian i1 f1 u))) *
        (∫ w in box N2 L, f2 w * f2 w) := by
  let u : X N1 → X N1 := fun x => x
  have hpt : (fun x : X (N1+N2) =>
        (prodState N1 N2 f1 f2 x) * (-(partialLaplacian (Fin.castAdd N2 i1) (prodState N1 N2 f1 f2) x))) =
      fun x : X (N1+N2) =>
        (f1 (firstBlock N1 N2 x) * (-(partialLaplacian i1 f1 (firstBlock N1 N2 x)))) *
          (f2 (lastBlock N1 N2 x) * f2 (lastBlock N1 N2 x)) := by
    funext x
    rw [partialLaplacian_prodState_first (f1 := f1) (f2 := f2) h1 i1 x]
    simp [prodState]
    ring
  rw [hpt]
  exact boxIntegral_prod_fun L (fun u : X N1 => f1 u * (-(partialLaplacian i1 f1 u)))
    (fun w : X N2 => f2 w * f2 w)

/-- A second-block kinetic term of the product state factorises. -/
lemma kinetic_term_last {N1 N2 : ℕ} {L : ℝ} {f1 : X N1 → ℝ} {f2 : X N2 → ℝ}
    (h2 : ContDiff ℝ 2 f2) (j2 : Fin N2) :
    (∫ x in box (N1+N2) L,
        (prodState N1 N2 f1 f2 x) * (-(partialLaplacian (Fin.natAdd N1 j2) (prodState N1 N2 f1 f2) x))) =
      (∫ u in box N1 L, f1 u * f1 u) *
        (∫ w in box N2 L, f2 w * (-(partialLaplacian j2 f2 w))) := by
  have hpt : (fun x : X (N1+N2) =>
        (prodState N1 N2 f1 f2 x) * (-(partialLaplacian (Fin.natAdd N1 j2) (prodState N1 N2 f1 f2) x))) =
      fun x : X (N1+N2) =>
        (f1 (firstBlock N1 N2 x) * f1 (firstBlock N1 N2 x)) *
          (f2 (lastBlock N1 N2 x) * (-(partialLaplacian j2 f2 (lastBlock N1 N2 x)))) := by
    funext x
    rw [partialLaplacian_prodState_last (f1 := f1) (f2 := f2) h2 j2 x]
    simp [prodState]
    ring
  rw [hpt]
  exact boxIntegral_prod_fun L (fun u : X N1 => f1 u * f1 u)
    (fun w : X N2 => f2 w * (-(partialLaplacian j2 f2 w)))


/-- A `C^∞` function is `C^2`. -/
lemma contDiff_two_of_infty {N : ℕ} {f : X N → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ 2 f := by
  have h : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := WithTop.coe_le_coe.mpr (by exact (le_top : (2 : ℕ∞) ≤ ⊤))
  exact hf.of_le h

/-! ## More translation and box-vanishing helpers -/

/-- The support of the shifted state lies in the shifted box. -/
lemma shifted_support_in_box {N : ℕ} {d L2 : ℝ} (hd0 : 0 ≤ d) (Φ2 : CInfty0Box N L2) :
    Function.support (shifted N d (Φ2 : X N → ℝ)) ⊆ box N (d + L2) := by
  intro w hw
  have hw2 : (addShift N d w) ∈ Function.support (Φ2 : X N → ℝ) := by
    exact shifted_support_preimage (N := N) (d := d) (f := (Φ2 : X N → ℝ)) hw
  have hw3 : (addShift N d w) ∈ box N L2 := support_subset_box_state Φ2 hw2
  rw [mem_box_iff]
  intro j k
  let c : ℝ := (w j).ofLp k
  have hjk : ((addShift N d w) j).ofLp k ∈ Set.Icc 0 L2 := ((mem_box_iff N L2 ((addShift N d w))).mp hw3) j k
  have hc : c - d ∈ Set.Icc 0 L2 := by
    simpa [c, addShift, offVec, sub_eq_add_neg] using hjk
  have hlo : 0 ≤ c := by linarith [hc.1, hd0]
  have hhi : c ≤ d + L2 := by linarith [hc.2]
  change c ∈ Set.Icc 0 (d + L2)
  exact ⟨hlo, hhi⟩

/-- An integral over the big box of a shifted-state function equals the whole-space integral. -/
lemma box_eq_whole_shifted_state {N : ℕ} {d L2 : ℝ} (hd0 : 0 ≤ d) (Φ2 : CInfty0Box N L2) {f : X N → ℝ}
    (hf : ∀ x, shifted N d (Φ2 : X N → ℝ) x = 0 → f x = 0) :
    (∫ x in box N (d + L2), f x) = ∫ x : X N, f x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  apply hf
  by_contra hz
  exact hx (shifted_support_in_box hd0 Φ2 hz)

/-- Whole-space integral invariance under the global shift. -/
lemma integral_shift {N : ℕ} (d : ℝ) (h : X N → ℝ) :
    (∫ w : X N, h (addShift N d w)) = ∫ z : X N, h z :=
  (addShift_measurePreserving' N d).integral_comp (addShift_measurableEmbedding N d) h

lemma shifted_eq_shift {N : ℕ} (d : ℝ) (f : X N → ℝ) :
    shifted N d f = fun w : X N => f (w - (fun _ : Fin N => offVec d)) := by
  funext w
  change f (addShift N d w) = f (w - (fun _ : Fin N => offVec d))
  apply congrArg f
  ext j
  simp [addShift, offVec, sub_eq_add_neg]

/-- `partialLaplacian` of the shifted state is the pullback of the original. -/
lemma partialLaplacian_addShift {N : ℕ} (d : ℝ) {f : X N → ℝ} (j : Fin N) (w : X N) :
    partialLaplacian j (shifted N d f) w = partialLaplacian j f (addShift N d w) := by
  rw [shifted_eq_shift]
  have htr := partialLaplacian_translate (N := N) (c := (fun _ : Fin N => offVec d)) (f := f) j w
  have hw : w - (fun _ : Fin N => offVec d) = addShift N d w := by
    ext j
    simp [addShift, offVec, sub_eq_add_neg]
  rw [hw] at htr
  exact htr

/-- The kinetic integrand of a shifted state equals the pullback of the original. -/
lemma kinP_shifted {N : ℕ} (d : ℝ) {f : X N → ℝ} (j : Fin N) (w : X N) :
    (shifted N d f w) * (-(partialLaplacian j (shifted N d f) w)) =
      (fun z : X N => f z * (-(partialLaplacian j f z))) (addShift N d w) := by
  rw [partialLaplacian_addShift d j w]
  simp [shifted]

lemma box_sq_integral_pos {N : ℕ} {L : ℝ} (hL : 0 < L) (Φ : CInfty0Box N L) :
    0 < ∫ x in box N L, (Φ : X N → ℝ) x * (Φ : X N → ℝ) x := by
  let f : X N → ℝ := fun x => (Φ : X N → ℝ) x * (Φ : X N → ℝ) x
  have hw : (∫ x in box N L, f x) = ∫ x : X N, f x := by
    apply box_eq_whole_of_state Φ
    intro x hz
    simp [f, hz]
  have hf0 : 0 ≤ f := by
    intro x
    dsimp [f]
    have h := sq_nonneg (Φ x)
    nlinarith
  have hcont : Continuous f := by
    dsimp [f]
    exact (psi_contDiff Φ).continuous.mul (psi_contDiff Φ).continuous
  have hcs : HasCompactSupport f := by
    have hsupp : Function.support f ⊆ Function.support (Φ : X N → ℝ) := by
      intro x hx
      by_contra hz
      apply hx
      have hΦ : (Φ : X N → ℝ) x = 0 := by
        by_cases hc : (Φ : X N → ℝ) x = 0
        · exact hc
        · exfalso
          exact hz hc
      simp [f, hΦ]
    have hts : tsupport f ⊆ tsupport (Φ : X N → ℝ) := by
      exact closure_mono hsupp
    exact IsCompact.of_isClosed_subset (tsupport_compact_of_box hL Φ) (isClosed_tsupport f) hts
  have hfi : Integrable f volume := Continuous.integrable_of_hasCompactSupport hcont hcs
  have hpos : 0 < ∫ x : X N, f x := by
    rw [MeasureTheory.integral_pos_iff_support_of_nonneg hf0 hfi]
    have hsup : Function.support f = {x : X N | (Φ : X N → ℝ) x ≠ 0} := by
      ext x
      by_cases hx : (Φ : X N → ℝ) x = 0 <;> simp [f, hx]
    rw [hsup]
    have hop : IsOpen {x : X N | (Φ : X N → ℝ) x ≠ 0} := (psi_contDiff Φ).continuous.isOpen_support
    have hne : ({x : X N | (Φ : X N → ℝ) x ≠ 0}).Nonempty := by
      by_contra hn
      have hz : (Φ : X N → ℝ) = 0 := by
        funext x
        by_contra hx
        exact hn ⟨x, hx⟩
      exact Φ.nezero hz
    exact IsOpen.measure_pos (μ := (volume : Measure (X N))) hop hne
  rw [hw]
  exact hpos

/-! ## The trial state's Rayleigh quotient is the sum of the two subsystem quotients -/

lemma boxQuot_trial_eq {N1 N2 : ℕ} {L L1 L2 R : ℝ} {v : ℝ³ → ℝ}
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hR : 0 ≤ R) (hL : L1 + L2 + R ≤ L)
    (hv1 : MemLp v 1) (hsupp : tsupport v ⊆ ball (0 : ℝ³) R)
    (Φ1 : CInfty0Box N1 L1) (Φ2 : CInfty0Box N2 L2) :
    boxQuot (N1+N2) L v (trialState N1 N2 hL1 hL2 hR hL Φ1 Φ2) =
      boxQuot N1 L1 v Φ1 + boxQuot N2 L2 v Φ2 := by
  let Ψ : CInfty0Box (N1+N2) L := trialState N1 N2 hL1 hL2 hR hL Φ1 Φ2
  let f1 : X N1 → ℝ := (Φ1 : X N1 → ℝ)
  let f2 : X N2 → ℝ := shifted N2 (L - L2) (Φ2 : X N2 → ℝ)
  let g : X (N1+N2) → ℝ := prodState N1 N2 f1 f2
  have hL3 : 0 < L := by linarith
  have hL1L : L1 ≤ L := by linarith
  have hL2L : L2 ≤ L := by linarith
  have hD : 0 ≤ L - L2 := by linarith
  have hg : (Ψ : X (N1+N2) → ℝ) = g := by
    rfl
  have h2c1 : ContDiff ℝ 2 f1 := contDiff_two_of_infty (psi_contDiff Φ1)
  have h2c2 : ContDiff ℝ 2 f2 := contDiff_two_of_infty (shifted_contDiff (psi_contDiff Φ2))
  -- -------- kinetic energy of the trial state --------
  have hsum1 : (∑ i1 : Fin N1, ∫ x in box (N1+N2) L,
          g x * (-(partialLaplacian (Fin.castAdd N2 i1) g x))) =
      (∑ i1 : Fin N1, ∫ u in box N1 L, f1 u * (-(partialLaplacian i1 f1 u))) *
        (∫ w in box N2 L, f2 w * f2 w) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i1 hi1
    have ht := kinetic_term_first (L := L) (f1 := f1) (f2 := f2) h2c1 i1
    simpa [g, prodState, f1, f2] using ht
  have hsum2 : (∑ j2 : Fin N2, ∫ x in box (N1+N2) L,
          g x * (-(partialLaplacian (Fin.natAdd N1 j2) g x))) =
      (∫ u in box N1 L, f1 u * f1 u) *
        (∑ j2 : Fin N2, ∫ w in box N2 L, f2 w * (-(partialLaplacian j2 f2 w))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j2 hj2
    have ht := kinetic_term_last (L := L) (f1 := f1) (f2 := f2) h2c2 j2
    simpa [g, prodState, f1, f2] using ht
  have hK3 : kineticEnergy (N1+N2) L Ψ =
      (∑ i1 : Fin N1, ∫ u in box N1 L, f1 u * (-(partialLaplacian i1 f1 u))) *
        (∫ w in box N2 L, f2 w * f2 w) +
      (∫ u in box N1 L, f1 u * f1 u) *
        (∑ j2 : Fin N2, ∫ w in box N2 L, f2 w * (-(partialLaplacian j2 f2 w))) := by
    calc
      kineticEnergy (N1+N2) L Ψ
          = ∑ i : Fin (N1+N2), ∫ x in box (N1+N2) L,
              (Ψ : X (N1+N2)→ℝ) x * (-(partialLaplacian i (Ψ : X (N1+N2)→ℝ) x)) := rfl
      _ = (∑ i1 : Fin N1, ∫ x in box (N1+N2) L,
              (Ψ : X (N1+N2)→ℝ) x * (-(partialLaplacian (Fin.castAdd N2 i1) (Ψ : X (N1+N2)→ℝ) x))) +
          (∑ j2 : Fin N2, ∫ x in box (N1+N2) L,
              (Ψ : X (N1+N2)→ℝ) x * (-(partialLaplacian (Fin.natAdd N1 j2) (Ψ : X (N1+N2)→ℝ) x))) := by
            rw [Fin.sum_univ_add]
      _ = (∑ i1 : Fin N1, ∫ x in box (N1+N2) L,
              g x * (-(partialLaplacian (Fin.castAdd N2 i1) g x))) +
          (∑ j2 : Fin N2, ∫ x in box (N1+N2) L,
              g x * (-(partialLaplacian (Fin.natAdd N1 j2) g x))) := by
            rfl
      _ = (∑ i1 : Fin N1, ∫ u in box N1 L, f1 u * (-(partialLaplacian i1 f1 u))) *
            (∫ w in box N2 L, f2 w * f2 w) +
          (∫ u in box N1 L, f1 u * f1 u) *
            (∑ j2 : Fin N2, ∫ w in box N2 L, f2 w * (-(partialLaplacian j2 f2 w))) := by
            rw [hsum1, hsum2]
  -- --------- interaction energy of the trial state ---------
  have hIint : (fun x : X (N1+N2) => intIntegrand (N1+N2) L v Ψ x) =
      fun x : X (N1+N2) => (g x)^2 * pairSum (N1+N2) v x := by
    funext x
    simp [intIntegrand, pairSum, hg]
  have hptI : (fun x : X (N1+N2) => (g x)^2 * pairSum (N1+N2) v x) =
      fun x : X (N1+N2) => (g x)^2 *
        (pairSum N1 v (firstBlock N1 N2 x) + pairSum N2 v (lastBlock N1 N2 x)) := by
    funext x
    have h := trial_int_pointwise (N1 := N1) (N2 := N2) (L := L) (L1 := L1) (L2 := L2) (R := R)
      hR hL hsupp Φ1 Φ2 x
    simpa [g, f1, f2, trialFun, prodState] using h
  -- integrability pieces
  have hc1 : Continuous f1 := (psi_contDiff Φ1).continuous
  have hc2 : Continuous f2 := (shifted_contDiff (psi_contDiff Φ2)).continuous
  have hintegrable_a1 : IntegrableOn (fun u : X N1 => (f1 u)^2 * pairSum N1 v u) (box N1 L) volume := by
    simpa [f1] using (integrableOn_state_int_big (N := N1) hL1 hL1L (v := v) hv1 Φ1)
  have hintegrable_b1 : IntegrableOn (fun w : X N2 => (f2 w)^2) (box N2 L) volume := by
    have hc : Continuous (fun w : X N2 => (f2 w)^2) := hc2.pow 2
    exact ContinuousOn.integrableOn_compact (box_compact hL3) hc.continuousOn
  have hintegrable_a2 : IntegrableOn (fun u : X N1 => (f1 u)^2) (box N1 L) volume := by
    have hc : Continuous (fun u : X N1 => (f1 u)^2) := hc1.pow 2
    exact ContinuousOn.integrableOn_compact (box_compact hL3) hc.continuousOn
  have hintegrable_b2 : IntegrableOn (fun w : X N2 => (f2 w)^2 * pairSum N2 v w) (box N2 L) volume := by
    have hh := integrableOn_int_shifted_big (N := N2) (d := L - L2) hL2 (v := v) hv1 Φ2
    have hbox : (L - L2) + L2 = L := by ring
    rw [hbox] at hh
    simpa [f2, shifted] using hh
  have hPint : IntegrableOn (fun x : X (N1+N2) => (g x)^2 * pairSum N1 v (firstBlock N1 N2 x))
      (box (N1+N2) L) volume := by
    have hprod := integrableOn_prod_box (N1 := N1) (N2 := N2) L
      (a := fun u : X N1 => (f1 u)^2 * pairSum N1 v u) (b := fun w : X N2 => (f2 w)^2)
      hintegrable_a1 hintegrable_b1
    -- convert: integrand = (f1(first)^2 * g1(first))·(f2(last)^2) vs (g x)^2·g1(first)
    convert hprod using 1
    · funext x
      -- (g x)^2·g1(u) = (f1u^2·g1(u))·(f2v^2): ring
      simp [g, prodState]
      ring
  have hQint : IntegrableOn (fun x : X (N1+N2) => (g x)^2 * pairSum N2 v (lastBlock N1 N2 x))
      (box (N1+N2) L) volume := by
    have hprod := integrableOn_prod_box (N1 := N1) (N2 := N2) L
      (a := fun u : X N1 => (f1 u)^2) (b := fun w : X N2 => (f2 w)^2 * pairSum N2 v w)
      hintegrable_a2 hintegrable_b2
    convert hprod using 1
    · funext x
      simp [g, prodState]
      ring
  have hI3 : interactionEnergy (N1+N2) L v Ψ =
      (∫ x in box (N1+N2) L, (g x)^2 * pairSum N1 v (firstBlock N1 N2 x)) +
      (∫ x in box (N1+N2) L, (g x)^2 * pairSum N2 v (lastBlock N1 N2 x)) := by
    calc
      interactionEnergy (N1+N2) L v Ψ
          = ∫ x in box (N1+N2) L, intIntegrand (N1+N2) L v Ψ x := by rw [boxInt_intIntegrand]
      _ = ∫ x in box (N1+N2) L, (g x)^2 * pairSum (N1+N2) v x := by rw [hIint]
      _ = ∫ x in box (N1+N2) L, (g x)^2 *
            (pairSum N1 v (firstBlock N1 N2 x) + pairSum N2 v (lastBlock N1 N2 x)) := by rw [hptI]
      _ = ∫ x in box (N1+N2) L,
            ((g x)^2 * pairSum N1 v (firstBlock N1 N2 x)) +
              ((g x)^2 * pairSum N2 v (lastBlock N1 N2 x)) := by
            apply integral_congr_ae
            filter_upwards with x
            ring
      _ = (∫ x in box (N1+N2) L, (g x)^2 * pairSum N1 v (firstBlock N1 N2 x)) +
          (∫ x in box (N1+N2) L, (g x)^2 * pairSum N2 v (lastBlock N1 N2 x)) := by
            rw [integral_add (μ := volume.restrict (box (N1+N2) L)) hPint hQint]
  have hPval : (∫ x in box (N1+N2) L, (g x)^2 * pairSum N1 v (firstBlock N1 N2 x)) =
      (∫ u in box N1 L, (f1 u)^2 * pairSum N1 v u) * (∫ w in box N2 L, f2 w * f2 w) := by
    calc
      (∫ x in box (N1+N2) L, (g x)^2 * pairSum N1 v (firstBlock N1 N2 x))
          = ∫ x in box (N1+N2) L,
              ((f1 (firstBlock N1 N2 x))^2 * pairSum N1 v (firstBlock N1 N2 x)) *
                ((f2 (lastBlock N1 N2 x))^2) := by
            apply integral_congr_ae
            filter_upwards with x
            simp [g, prodState]
            ring
      _ = (∫ u in box N1 L, (f1 u)^2 * pairSum N1 v u) * (∫ w in box N2 L, (f2 w)^2) := by
            exact boxIntegral_prod_fun L (fun u : X N1 => (f1 u)^2 * pairSum N1 v u)
              (fun w : X N2 => (f2 w)^2)
      _ = (∫ u in box N1 L, (f1 u)^2 * pairSum N1 v u) * (∫ w in box N2 L, f2 w * f2 w) := by
            have hp : (∫ w in box N2 L, (f2 w)^2) = ∫ w in box N2 L, f2 w * f2 w := by
              congr 1
              funext w
              rw [pow_two]
            rw [hp]
  have hQval : (∫ x in box (N1+N2) L, (g x)^2 * pairSum N2 v (lastBlock N1 N2 x)) =
      (∫ u in box N1 L, f1 u * f1 u) * (∫ w in box N2 L, (f2 w)^2 * pairSum N2 v w) := by
    calc
      (∫ x in box (N1+N2) L, (g x)^2 * pairSum N2 v (lastBlock N1 N2 x))
          = ∫ x in box (N1+N2) L,
              ((f1 (firstBlock N1 N2 x))^2) *
                ((f2 (lastBlock N1 N2 x))^2 * pairSum N2 v (lastBlock N1 N2 x)) := by
            apply integral_congr_ae
            filter_upwards with x
            simp [g, prodState]
            ring
      _ = (∫ u in box N1 L, (f1 u)^2) * (∫ w in box N2 L, (f2 w)^2 * pairSum N2 v w) := by
            exact boxIntegral_prod_fun L (fun u : X N1 => (f1 u)^2)
              (fun w : X N2 => (f2 w)^2 * pairSum N2 v w)
      _ = (∫ u in box N1 L, f1 u * f1 u) * (∫ w in box N2 L, (f2 w)^2 * pairSum N2 v w) := by
            have hp : (∫ u in box N1 L, (f1 u)^2) = ∫ u in box N1 L, f1 u * f1 u := by
              congr 1
              funext u
              rw [pow_two]
            rw [hp]
  -- --------- denominator ---------
  have hden3 : (∫ x in box (N1+N2) L, (g x) * (g x)) =
      (∫ u in box N1 L, f1 u * f1 u) * (∫ w in box N2 L, f2 w * f2 w) := by
    calc
      (∫ x in box (N1+N2) L, (g x) * (g x))
          = ∫ x in box (N1+N2) L, ((f1 (firstBlock N1 N2 x)) * (f1 (firstBlock N1 N2 x))) *
              ((f2 (lastBlock N1 N2 x)) * (f2 (lastBlock N1 N2 x))) := by
            apply integral_congr_ae
            filter_upwards with x
            simp [g, prodState]
            ring
      _ = (∫ u in box N1 L, f1 u * f1 u) * (∫ w in box N2 L, f2 w * f2 w) := by
            exact boxIntegral_prod_fun L (fun u : X N1 => f1 u * f1 u) (fun w : X N2 => f2 w * f2 w)
  -- --------- small-box identities ---------
  have hA1L : (∫ u in box N1 L, f1 u * f1 u) = (∫ u in box N1 L1, f1 u * f1 u) := by
    apply integral_box_eq_of_le hL1L
    intro u hu
    have hz : f1 u = 0 := by simpa [f1] using (psi_eq_zero_of_not_mem_box Φ1 hu)
    simp [hz]
  have hA2L : (∫ w in box N2 L, f2 w * f2 w) = (∫ z in box N2 L2, (Φ2 : X N2 → ℝ) z * (Φ2 : X N2 → ℝ) z) := by
    have h1 : (∫ w in box N2 L, f2 w * f2 w) = ∫ w : X N2, f2 w * f2 w := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro w hw
      have hs : Function.support f2 ⊆ box N2 L := by
        have hb := shifted_support_in_box (N := N2) hD Φ2
        have hbox : (L - L2) + L2 = L := by ring
        rw [hbox] at hb
        simpa [f2] using hb
      have hz : f2 w = 0 := by
        by_contra h2
        exact hw (hs (by simpa using h2))
      simp [hz]
    have h2 : (∫ w : X N2, f2 w * f2 w) = ∫ z : X N2, (Φ2 : X N2 → ℝ) z * (Φ2 : X N2 → ℝ) z := by
      have hpt : (fun w : X N2 => f2 w * f2 w) =
          (fun z : X N2 => (Φ2 : X N2 → ℝ) z * (Φ2 : X N2 → ℝ) z) ∘ (addShift N2 (L - L2)) := by
        funext w
        simp [f2, shifted, Function.comp_def]
      rw [hpt]
      exact integral_shift (N := N2) (L - L2) (fun z => (Φ2 : X N2 → ℝ) z * (Φ2 : X N2 → ℝ) z)
    have h3 : (∫ z : X N2, (Φ2 : X N2 → ℝ) z * (Φ2 : X N2 → ℝ) z) =
        ∫ z in box N2 L2, (Φ2 : X N2 → ℝ) z * (Φ2 : X N2 → ℝ) z := by
      exact (box_eq_whole_of_state Φ2 (fun x hz => by simp [hz])).symm
    rw [h1, h2, h3]
  have hK1L : (∑ i1 : Fin N1, ∫ u in box N1 L, f1 u * (-(partialLaplacian i1 f1 u))) =
      kineticEnergy N1 L1 Φ1 := by
    calc
      (∑ i1 : Fin N1, ∫ u in box N1 L, f1 u * (-(partialLaplacian i1 f1 u)))
          = ∑ i1 : Fin N1, ∫ u in box N1 L1, f1 u * (-(partialLaplacian i1 f1 u)) := by
            apply Finset.sum_congr rfl
            intro i1 hi1
            apply integral_box_eq_of_le hL1L
            intro u hu
            have hz : f1 u = 0 := by simpa [f1] using (psi_eq_zero_of_not_mem_box Φ1 hu)
            simp [hz]
      _ = kineticEnergy N1 L1 Φ1 := by
            unfold kineticEnergy
            rfl
  have hI1L : (∫ u in box N1 L, (f1 u)^2 * pairSum N1 v u) = interactionEnergy N1 L1 v Φ1 := by
    calc
      (∫ u in box N1 L, (f1 u)^2 * pairSum N1 v u)
          = ∫ u in box N1 L1, (f1 u)^2 * pairSum N1 v u := by
            apply integral_box_eq_of_le hL1L
            intro u hu
            have hz : f1 u = 0 := by simpa [f1] using (psi_eq_zero_of_not_mem_box Φ1 hu)
            simp [hz]
      _ = ∫ u in box N1 L1, intIntegrand N1 L1 v Φ1 u := by
            apply integral_congr_ae
            filter_upwards with u
            rfl
      _ = interactionEnergy N1 L1 v Φ1 := by
            rw [boxInt_intIntegrand]
  have hK2L : (∑ j2 : Fin N2, ∫ w in box N2 L, f2 w * (-(partialLaplacian j2 f2 w))) =
      kineticEnergy N2 L2 Φ2 := by
    calc
      (∑ j2 : Fin N2, ∫ w in box N2 L, f2 w * (-(partialLaplacian j2 f2 w)))
          = ∑ j2 : Fin N2, ∫ w in box N2 L2,
              (Φ2 : X N2 → ℝ) w * (-(partialLaplacian j2 (Φ2 : X N2 → ℝ) w)) := by
            apply Finset.sum_congr rfl
            intro j2 hj2
            calc
              (∫ w in box N2 L, f2 w * (-(partialLaplacian j2 f2 w)))
                  = ∫ w : X N2, f2 w * (-(partialLaplacian j2 f2 w)) := by
                    apply setIntegral_eq_integral_of_forall_compl_eq_zero
                    intro w hw
                    have hs : Function.support f2 ⊆ box N2 L := by
                      have hb := shifted_support_in_box (N := N2) hD Φ2
                      have hbox : (L - L2) + L2 = L := by ring
                      rw [hbox] at hb
                      simpa [f2] using hb
                    have hz : f2 w = 0 := by
                      by_contra h2
                      exact hw (hs (by simpa using h2))
                    simp [hz]
              _ = ∫ w : X N2,
                    (Φ2 : X N2 → ℝ) (addShift N2 (L - L2) w) *
                      (-(partialLaplacian j2 (Φ2 : X N2 → ℝ) (addShift N2 (L - L2) w))) := by
                    have hpt : (fun w : X N2 => f2 w * (-(partialLaplacian j2 f2 w))) =
                        (fun z : X N2 => (Φ2 : X N2 → ℝ) z * (-(partialLaplacian j2 (Φ2 : X N2 → ℝ) z))) ∘
                          (addShift N2 (L - L2)) := by
                      funext w
                      have hk := kinP_shifted (N := N2) (L - L2) (f := (Φ2 : X N2 → ℝ)) j2 w
                      simpa [f2, Function.comp_def, shifted] using hk
                    rw [hpt]
                    rfl
              _ = ∫ z : X N2, (Φ2 : X N2 → ℝ) z * (-(partialLaplacian j2 (Φ2 : X N2 → ℝ) z)) := by
                    exact integral_shift (N := N2) (L - L2)
                      (fun z => (Φ2 : X N2 → ℝ) z * (-(partialLaplacian j2 (Φ2 : X N2 → ℝ) z)))
              _ = ∫ w in box N2 L2, (Φ2 : X N2 → ℝ) w * (-(partialLaplacian j2 (Φ2 : X N2 → ℝ) w)) := by
                    exact (box_eq_whole_of_state Φ2 (fun x hz => by simp [hz])).symm
      _ = kineticEnergy N2 L2 Φ2 := by
            unfold kineticEnergy
            rfl
  have hI2L : (∫ w in box N2 L, (f2 w)^2 * pairSum N2 v w) = interactionEnergy N2 L2 v Φ2 := by
    calc
      (∫ w in box N2 L, (f2 w)^2 * pairSum N2 v w)
          = ∫ w : X N2, (f2 w)^2 * pairSum N2 v w := by
            apply setIntegral_eq_integral_of_forall_compl_eq_zero
            intro w hw
            have hs : Function.support f2 ⊆ box N2 L := by
              have hb := shifted_support_in_box (N := N2) hD Φ2
              have hbox : (L - L2) + L2 = L := by ring
              rw [hbox] at hb
              simpa [f2] using hb
            have hz : f2 w = 0 := by
              by_contra h2
              exact hw (hs (by simpa using h2))
            simp [hz]
      _ = ∫ w : X N2, (Φ2 : X N2 → ℝ) (addShift N2 (L - L2) w)^2 *
            pairSum N2 v (addShift N2 (L - L2) w) := by
            apply integral_congr_ae
            filter_upwards with w
            have hk := intP_shifted (N := N2) v (L - L2) (Φ2 : X N2 → ℝ) w
            simpa [f2, shifted] using hk
      _ = ∫ z : X N2, (Φ2 : X N2 → ℝ) z^2 * pairSum N2 v z := by
            have hpt2 : (fun w : X N2 => (Φ2 : X N2 → ℝ) (addShift N2 (L - L2) w)^2 *
                pairSum N2 v (addShift N2 (L - L2) w)) =
              (fun z : X N2 => (Φ2 : X N2 → ℝ) z^2 * pairSum N2 v z) ∘ (addShift N2 (L - L2)) := by
              funext w
              rfl
            rw [hpt2]
            exact integral_shift (N := N2) (L - L2) (fun z => (Φ2 : X N2 → ℝ) z^2 * pairSum N2 v z)
      _ = ∫ z in box N2 L2, (Φ2 : X N2 → ℝ) z^2 * pairSum N2 v z := by
            exact (box_eq_whole_of_state Φ2 (fun x hz => by simp [hz])).symm
      _ = ∫ z in box N2 L2, intIntegrand N2 L2 v Φ2 z := by
            apply integral_congr_ae
            filter_upwards with z
            rfl
      _ = interactionEnergy N2 L2 v Φ2 := by
            rw [boxInt_intIntegrand]

  -- -------- numerator and quotient --------
  let num1 : ℝ := ∫ u in box N1 L1, f1 u * 𝓗 N1 v f1 u
  let den1 : ℝ := ∫ u in box N1 L1, f1 u * f1 u
  let num2 : ℝ := ∫ z in box N2 L2, (Φ2 : X N2 → ℝ) z * 𝓗 N2 v (Φ2 : X N2 → ℝ) z
  let den2 : ℝ := ∫ z in box N2 L2, (Φ2 : X N2 → ℝ) z * (Φ2 : X N2 → ℝ) z
  let num3 : ℝ := ∫ x in box (N1+N2) L, g x * 𝓗 (N1+N2) v g x
  let den3 : ℝ := ∫ x in box (N1+N2) L, g x * g x
  have hdec1 : num1 = kineticEnergy N1 L1 Φ1 + interactionEnergy N1 L1 v Φ1 := by
    have h := energy_decomposition_admissible N1 hL1 (v := v) hv1 Φ1
    simpa [num1, f1] using h
  have hdec2 : num2 = kineticEnergy N2 L2 Φ2 + interactionEnergy N2 L2 v Φ2 := by
    exact energy_decomposition_admissible N2 hL2 (v := v) hv1 Φ2
  have hdec3 : num3 = kineticEnergy (N1+N2) L Ψ + interactionEnergy (N1+N2) L v Ψ := by
    have h := energy_decomposition_admissible (N1+N2) hL3 (v := v) hv1 Ψ
    simpa [num3, hg] using h
  have hnum3 : num3 = num1 * den2 + den1 * num2 := by
    calc
      num3 = kineticEnergy (N1+N2) L Ψ + interactionEnergy (N1+N2) L v Ψ := hdec3
      _ = ((∑ i1 : Fin N1, ∫ u in box N1 L, f1 u * (-(partialLaplacian i1 f1 u))) *
            (∫ w in box N2 L, f2 w * f2 w) +
          (∫ u in box N1 L, f1 u * f1 u) *
            (∑ j2 : Fin N2, ∫ w in box N2 L, f2 w * (-(partialLaplacian j2 f2 w)))) +
          ((∫ u in box N1 L, (f1 u)^2 * pairSum N1 v u) * (∫ w in box N2 L, f2 w * f2 w) +
            (∫ u in box N1 L, f1 u * f1 u) * (∫ w in box N2 L, (f2 w)^2 * pairSum N2 v w)) := by
            rw [hK3, hI3, hPval, hQval]
      _ = (kineticEnergy N1 L1 Φ1 * den2 + den1 * kineticEnergy N2 L2 Φ2) +
            (interactionEnergy N1 L1 v Φ1 * den2 + den1 * interactionEnergy N2 L2 v Φ2) := by
            rw [hK1L, hK2L, hI1L, hI2L, hA1L, hA2L]
      _ = (kineticEnergy N1 L1 Φ1 + interactionEnergy N1 L1 v Φ1) * den2 +
            den1 * (kineticEnergy N2 L2 Φ2 + interactionEnergy N2 L2 v Φ2) := by
            ring
      _ = num1 * den2 + den1 * num2 := by
            rw [hdec1, hdec2]
  have hden3E : den3 = den1 * den2 := by
    change (∫ x in box (N1+N2) L, g x * g x) =
      (∫ u in box N1 L1, f1 u * f1 u) * (∫ z in box N2 L2, (Φ2 : X N2 → ℝ) z * (Φ2 : X N2 → ℝ) z)
    rw [hden3, hA1L, hA2L]
  have hpos1 : 0 < den1 := by
    have h := box_sq_integral_pos (N := N1) hL1 Φ1
    simpa [den1, f1] using h
  have hpos2 : 0 < den2 := by
    simpa [den2] using (box_sq_integral_pos (N := N2) hL2 Φ2)
  have hq3 : boxQuot (N1+N2) L v Ψ = num3 / den3 := by
    unfold boxQuot
    have hn : (∫ x in box (N1+N2) L, (Ψ : X (N1+N2)→ℝ) x * 𝓗 (N1+N2) v (Ψ : X (N1+N2)→ℝ) x) = num3 := by
      simp [hg, num3]
    have hd : (∫ x in box (N1+N2) L, (Ψ : X (N1+N2)→ℝ) x * (Ψ : X (N1+N2)→ℝ) x) = den3 := by
      simp [hg, den3]
    have hpos : 0 ≤ den3 := by
      rw [hden3E]
      exact mul_nonneg (le_of_lt hpos1) (le_of_lt hpos2)
    rw [hn, hd]
    rw [Real.sq_sqrt hpos]
  have hq1 : boxQuot N1 L1 v Φ1 = num1 / den1 := by
    unfold boxQuot
    have hn : (∫ u in box N1 L1, (Φ1 : X N1 → ℝ) u * 𝓗 N1 v (Φ1 : X N1 → ℝ) u) = num1 := by
      simp [num1, f1]
    have hd : (∫ u in box N1 L1, (Φ1 : X N1 → ℝ) u * (Φ1 : X N1 → ℝ) u) = den1 := by
      simp [den1, f1]
    rw [hn, hd]
    rw [Real.sq_sqrt (le_of_lt hpos1)]
  have hq2 : boxQuot N2 L2 v Φ2 = num2 / den2 := by
    unfold boxQuot
    have hn : (∫ z in box N2 L2, (Φ2 : X N2 → ℝ) z * 𝓗 N2 v (Φ2 : X N2 → ℝ) z) = num2 := by
      simp [num2]
    have hd : (∫ z in box N2 L2, (Φ2 : X N2 → ℝ) z * (Φ2 : X N2 → ℝ) z) = den2 := by
      simp [den2]
    rw [hn, hd]
    rw [Real.sq_sqrt (le_of_lt hpos2)]
  have hq : num3 / den3 = num1 / den1 + num2 / den2 := by
    rw [hnum3, hden3E]
    field_simp [ne_of_gt hpos1, ne_of_gt hpos2]
  rw [hq3, hq1, hq2, hq]

/-- The Rayleigh quotient of any state is nonnegative. -/
lemma boxQuot_nonneg {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L) (hv : 0 ≤ v)
    (Φ : CInfty0Box N L) : 0 ≤ boxQuot N L v Φ := by
  unfold boxQuot
  exact div_nonneg (boxEnergy_num_nonneg hL hv Φ) (sq_nonneg _)

/-- Subadditivity of the box energy over separated volumes. -/
lemma boxEnergy_subadd {N1 N2 : ℕ} {L L1 L2 R : ℝ} {v : ℝ³ → ℝ}
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hR : 0 ≤ R) (hL : L1 + L2 + R ≤ L)
    (hv : 0 ≤ v) (hv1 : MemLp v 1) (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) :
    boxEnergy (N1+N2) L v ≤ boxEnergy N1 L1 v + boxEnergy N2 L2 v := by
  have hL3 : 0 < L := by linarith
  have hne1 : Nonempty (CInfty0Box N1 L1) := nonempty_CInfty0Box N1 hL1
  have hne2 : Nonempty (CInfty0Box N2 L2) := nonempty_CInfty0Box N2 hL2
  have hmain : ∀ (Φ1 : CInfty0Box N1 L1) (Φ2 : CInfty0Box N2 L2),
      boxEnergy (N1+N2) L v ≤ boxQuot N1 L1 v Φ1 + boxQuot N2 L2 v Φ2 := by
    intro Φ1 Φ2
    let Ψ : CInfty0Box (N1+N2) L := trialState N1 N2 hL1 hL2 hR hL Φ1 Φ2
    have hq := boxQuot_trial_eq (N1 := N1) (N2 := N2) (L := L) (L1 := L1) (L2 := L2) (R := R)
      (v := v) hL1 hL2 hR hL hv1 hsupp Φ1 Φ2
    have hinfle : boxEnergy (N1+N2) L v ≤ boxQuot (N1+N2) L v Ψ := by
      rw [boxEnergy_eq_ciInf_boxQuot]
      have hbdd : BddBelow (Set.range (boxQuot (N1+N2) L v)) := by
        refine ⟨0, ?_⟩
        rintro y ⟨Φ, rfl⟩
        exact boxQuot_nonneg hL3 hv Φ
      exact ciInf_le hbdd Ψ
    calc
      boxEnergy (N1+N2) L v ≤ boxQuot (N1+N2) L v Ψ := hinfle
      _ = boxQuot N1 L1 v Φ1 + boxQuot N2 L2 v Φ2 := hq
  have hstep1 : ∀ Φ1 : CInfty0Box N1 L1,
      boxEnergy (N1+N2) L v - boxQuot N1 L1 v Φ1 ≤ boxEnergy N2 L2 v := by
    intro Φ1
    have hle2 : ∀ Φ2 : CInfty0Box N2 L2,
        boxEnergy (N1+N2) L v - boxQuot N1 L1 v Φ1 ≤ boxQuot N2 L2 v Φ2 := by
      intro Φ2
      linarith [hmain Φ1 Φ2]
    rw [boxEnergy_eq_ciInf_boxQuot]
    haveI := hne2
    exact le_ciInf hle2
  have hstep2 : boxEnergy (N1+N2) L v - boxEnergy N2 L2 v ≤ boxEnergy N1 L1 v := by
    have hle1 : ∀ Φ1 : CInfty0Box N1 L1,
        boxEnergy (N1+N2) L v - boxEnergy N2 L2 v ≤ boxQuot N1 L1 v Φ1 := by
      intro Φ1
      linarith [hstep1 Φ1]
    rw [boxEnergy_eq_ciInf_boxQuot]
    haveI := hne1
    exact le_ciInf hle1
  linarith

end BoseGases

end Submission
