import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Dihedral.mulEquiv_dihedral_of_cyclic_index_two
import Submission.Work.L2F.Mat2.pslMap_eq_one_iff
import Submission.Work.L2F.PSL.mem_normalizer_torus_iff
import Submission.Work.L2F.PSL.pslSplitTorus_card
import Submission.Work.L2F.PSL.pslSplitTorus_isCyclic
import Submission.Work.L2F.Involution.orderOf_pslZ

open scoped MatrixGroups
open Matrix

namespace Work.L2F.PSL

/-!
# The normalizer of the split torus image in `PSL(2,F)`

Main result (`normalizer_pslSplitTorus_dihedral`): the normalizer in `PSL(2,F)` of
`pslSplitTorus F = π(T)`, the image of the split (diagonal) torus `T = torus F`, is dihedral of
order `2 * |π(T)| = q - 1` for `q = |F| ≥ 5`.

The proof has three layers.

* `mem_map_torus_iff`: `π(x) ∈ π(T) ↔ x ∈ T`, because `ker π = Z(SL(2,F)) = {±1} ⊆ T`.
* `normalizer_pslSplitTorus_eq_map`: `N_{PSL}(π(T)) = π(N_{SL}(T))`, the two inclusions being
  `h ↦ π h` (a homomorphism sends normalizer to normalizer) and the lift of `g ∈ N_{PSL}(π(T))`
  to `x ∈ SL(2,F)` via the surjectivity of `π`, together with the previous point.
* `mem_normalizer_torus_iff` (a separate file): `N_{SL(2,F)}(T) = T ∪ zT` where
  `z = weyl = !![0,1;-1,0]` normalizes and inverts `T` (`z diag(a,a⁻¹) z⁻¹ = diag(a⁻¹,a)`) and
  `z² = -1 ∈ T`.

Hence `N_{PSL}(π(T)) = π(T) ⊔ ⟨π(z)⟩`, with `π(T)` cyclic (an image of `Fˣ`) and of index two,
and `π(z)` an involution outside it inverting it, so
`Work.L2F.Dihedral.mulEquiv_dihedral_of_cyclic_index_two` applies.
-/

/-! ## `π(x) ∈ π(T) ↔ x ∈ T` -/

/-- The kernel of `SL(2,F) → PSL(2,F)` is `{±1}`, and both `1` and `-1 = diag (-1)` lie in the
split torus, so `ker π ≤ T`. -/
lemma pslMap_ker_le_torus (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) :
    (Work.PSL2.pslMap F).ker ≤ Work.L2F.torus F := by
  intro y hy
  rw [MonoidHom.mem_ker] at hy
  rcases (Work.L2F.Mat2.pslMap_eq_one_iff F h2 y).mp hy with h | h
  · rw [h]; exact Subgroup.one_mem _
  · rw [h, Work.L2F.torus, MonoidHom.mem_range]
    exact ⟨-1, (diag_eq_negOne_iff F (-1)).mpr rfl⟩

/-- `π(x) ∈ π(T) = pslSplitTorus F` if and only if `x ∈ T = torus F`: `π(x) = π(t)` for some
`t ∈ T` iff `x t⁻¹ ∈ ker π ⊆ T`. -/
lemma mem_map_torus_iff (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (x : Matrix.SpecialLinearGroup (Fin 2) F) :
    Work.PSL2.pslMap F x ∈ (Work.L2F.torus F).map (Work.PSL2.pslMap F) ↔
      x ∈ Work.L2F.torus F := by
  constructor
  · rintro ⟨t, ht, ht_eq⟩
    have hker : x * t⁻¹ ∈ (Work.PSL2.pslMap F).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ht_eq, mul_inv_cancel]
    have hmem : x * t⁻¹ ∈ Work.L2F.torus F := pslMap_ker_le_torus F h2 hker
    have hx : x = (x * t⁻¹) * t := by group
    rw [hx]
    exact (Work.L2F.torus F).mul_mem hmem ht
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- `z = !![0,1;-1,0]` is not diagonal, hence not in the split torus. -/
lemma z_notMem_torus (F : Type*) [Field F] : Work.L2F.z F ∉ Work.L2F.torus F := by
  intro hz
  rw [Work.L2F.torus, MonoidHom.mem_range] at hz
  obtain ⟨a, ha⟩ := hz
  have ha' : Work.PSL2.diag F a = Work.L2F.z F := ha
  have hmat := congrArg (fun x : SL(2, F) => ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) ha'
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) hmat
  rw [Work.PSL2.coe_diag, Work.L2F.z, Work.PSL2.coe_weyl] at h00
  simp at h00

/-! ## `N_{PSL}(π(T)) = π(N_{SL}(T))` -/

/-- The image of a normalizer of a subgroup is contained in the normalizer of the image:
conjugation commutes with a homomorphism. -/
lemma map_normalizer_le (F : Type*) [Field F] :
    (Subgroup.normalizer (Work.L2F.torus F : Set (Matrix.SpecialLinearGroup (Fin 2) F))).map
        (Work.PSL2.pslMap F) ≤
      Subgroup.normalizer (Work.L2F.pslSplitTorus F :
        Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) := by
  rintro g ⟨x, hxN, rfl⟩
  have hxN' : ∀ h : Matrix.SpecialLinearGroup (Fin 2) F,
      h ∈ Work.L2F.torus F ↔ x * h * x⁻¹ ∈ Work.L2F.torus F :=
    Subgroup.mem_normalizer_iff.mp hxN
  refine Subgroup.mem_normalizer_iff.mpr ?_
  intro y
  constructor
  · intro hy
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hy
    refine Subgroup.mem_map.mpr ⟨x * t * x⁻¹, (hxN' t).mp ht, ?_⟩
    rw [map_mul, map_inv, map_mul]
  · intro hy
    obtain ⟨s, hs, hs_eq⟩ := Subgroup.mem_map.mp hy
    refine Subgroup.mem_map.mpr ⟨x⁻¹ * s * x, (hxN' (x⁻¹ * s * x)).mpr ?_, ?_⟩
    · rw [show x * (x⁻¹ * s * x) * x⁻¹ = s from by group]; exact hs
    · rw [map_mul, map_mul, map_inv, hs_eq]; group

/-- `N_{PSL(2,F)}(π(T)) = π(N_{SL(2,F)}(T))`: this is the `π`-transfer of the normalizer.
`⊆`: lift `g ∈ N(π(T))` to `x ∈ SL(2,F)`; `π(x) π(T) π(x)⁻¹ = π(T)` reads `π(x T x⁻¹) = π(T)`,
and since `ker π ⊆ T` this gives `x T x⁻¹ = T`. `⊇`: `π` is a homomorphism. -/
theorem normalizer_pslSplitTorus_eq_map (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) :
    Subgroup.normalizer (Work.L2F.pslSplitTorus F :
        Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) =
      (Subgroup.normalizer (Work.L2F.torus F :
        Set (Matrix.SpecialLinearGroup (Fin 2) F))).map (Work.PSL2.pslMap F) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center (SL(2, F))) g
    have hx' : Work.PSL2.pslMap F x = g := hx
    have hg' : ∀ h : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F,
        h ∈ Work.L2F.pslSplitTorus F ↔ g * h * g⁻¹ ∈ Work.L2F.pslSplitTorus F :=
      Subgroup.mem_normalizer_iff.mp hg
    have hxN : x ∈ Subgroup.normalizer (Work.L2F.torus F :
        Set (Matrix.SpecialLinearGroup (Fin 2) F)) := by
      refine Subgroup.mem_normalizer_iff.mpr ?_
      intro h
      have hh := hg' (Work.PSL2.pslMap F h)
      rw [← mem_map_torus_iff F h2 h, ← mem_map_torus_iff F h2 (x * h * x⁻¹)]
      have heq : g * Work.PSL2.pslMap F h * g⁻¹ = Work.PSL2.pslMap F (x * h * x⁻¹) := by
        rw [← hx', ← map_inv, ← map_mul, ← map_mul]
      rw [← heq]
      exact hh
    exact Subgroup.mem_map.mpr ⟨x, hxN, hx'⟩
  · exact map_normalizer_le F

/-! ## The Weyl element normalizes and inverts the split torus -/

/-- `z * diag a = diag (a⁻¹) * z`, the Weyl relation in matrix form (no group inverse needed).
Equivalently `z diag(a,a⁻¹) z⁻¹ = diag(a⁻¹,a)`. -/
lemma z_mul_diag (F : Type*) [Field F] (a : Fˣ) :
    Work.L2F.z F * Work.PSL2.diag F a = Work.PSL2.diag F a⁻¹ * Work.L2F.z F := by
  apply Subtype.ext
  change ((Work.L2F.z F * Work.PSL2.diag F a : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
    ((Work.PSL2.diag F a⁻¹ * Work.L2F.z F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Work.PSL2.coe_diag, Work.PSL2.coe_diag, Work.L2F.z, Work.PSL2.coe_weyl,
    Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `z t z⁻¹ = t⁻¹` for `t ∈ T`: the Weyl element inverts the split torus. -/
lemma z_conj_inv_diag (F : Type*) [Field F] (a : Fˣ) :
    Work.L2F.z F * Work.PSL2.diag F a * (Work.L2F.z F)⁻¹ = Work.PSL2.diag F a⁻¹ := by
  rw [z_mul_diag F a, mul_assoc, mul_inv_cancel, mul_one]

/-- The image `π(z) = pslWeyl F` of the Weyl element is an involution. -/
lemma pslWeyl_mul_self (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) :
    Work.PSL2.pslWeyl F * Work.PSL2.pslWeyl F = 1 := by
  have h : Work.L2F.pslZ F ^ 2 = 1 := by
    have h1 := pow_orderOf_eq_one (Work.L2F.pslZ F)
    rw [Work.L2F.Involution.orderOf_pslZ F h2] at h1
    exact h1
  simpa [pow_two, Work.L2F.pslZ] using h

/-- `pslWeyl F` is not in `pslSplitTorus F`: its lift `z` is not diagonal. -/
lemma pslWeyl_notMem (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) :
    Work.PSL2.pslWeyl F ∉ Work.L2F.pslSplitTorus F := by
  intro hmem
  have h : Work.PSL2.pslWeyl F = Work.PSL2.pslMap F (Work.L2F.z F) := rfl
  rw [h] at hmem
  exact z_notMem_torus F ((mem_map_torus_iff F h2 (Work.L2F.z F)).mp hmem)

/-- `pslWeyl F` inverts `pslSplitTorus F` by conjugation. -/
lemma pslWeyl_inverts (F : Type*) [Field F] (_h2 : (2 : F) ≠ 0) :
    ∀ c ∈ Work.L2F.pslSplitTorus F,
      Work.PSL2.pslWeyl F * c * (Work.PSL2.pslWeyl F)⁻¹ = c⁻¹ := by
  intro c hc
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hc
  have hz : Work.PSL2.pslWeyl F = Work.PSL2.pslMap F (Work.L2F.z F) := rfl
  have key : Work.PSL2.pslWeyl F * Work.PSL2.pslMap F t * (Work.PSL2.pslWeyl F)⁻¹ =
      Work.PSL2.pslMap F (Work.L2F.z F * t * (Work.L2F.z F)⁻¹) := by
    rw [hz, ← map_mul, ← map_inv, ← map_mul]
  rw [key, ← map_inv]
  congr 1
  rw [Work.L2F.torus, MonoidHom.mem_range] at ht
  obtain ⟨a, rfl⟩ := ht
  change Work.L2F.z F * Work.PSL2.diag F a * (Work.L2F.z F)⁻¹ = (Work.PSL2.diag F a)⁻¹
  rw [z_conj_inv_diag F a]
  exact (map_inv (Work.PSL2.diagHom F) a)

/-- `pslWeyl F` lies in the normalizer of `pslSplitTorus F`: `z` normalizes `T`. -/
lemma pslWeyl_mem_normalizer (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (h5 : 5 ≤ Nat.card F) :
    Work.PSL2.pslWeyl F ∈ Subgroup.normalizer (Work.L2F.pslSplitTorus F :
      Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) := by
  rw [normalizer_pslSplitTorus_eq_map F h2]
  refine Subgroup.mem_map.mpr ⟨Work.L2F.z F, ?_, rfl⟩
  exact (mem_normalizer_torus_iff F h2 h5 (Work.L2F.z F)).mpr
    (Or.inr ⟨1, Subgroup.one_mem _, by rw [mul_one]⟩)

/-! ## The main theorem -/

/-- The normalizer in `PSL(2,F)` of the split torus image is dihedral of order `q - 1`, i.e. of
order `2 * Nat.card (pslSplitTorus F)` (for `q ≥ 5`).  Proof: `N_{PSL}(π(T)) = π(N_{SL}(T))` and
`N_{SL}(T) = T ∪ z T` where `z = weyl = !![0,1;-1,0]` satisfies `z * T * z⁻¹ = T` and inverts it
(`z diag(a,a⁻¹) z⁻¹ = diag(a⁻¹,a)`), with `z² = -1`; in `PSL`, `π(T)` is cyclic of index two and
`π(z)` is an involution outside it inverting it, so `mulEquiv_dihedral_of_cyclic_index_two` applies
(`π(T) = pslSplitTorus F` is cyclic as the image of the cyclic group `Fˣ`).  The hypothesis
`5 ≤ Nat.card F` is needed: for `q = 3` the split torus image is trivial and the statement fails. -/
theorem normalizer_pslSplitTorus_dihedral (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (h5 : 5 ≤ Nat.card F) :
    Nonempty (Subgroup.normalizer (Work.L2F.pslSplitTorus F :
        Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) ≃*
      DihedralGroup (Nat.card (Work.L2F.pslSplitTorus F))) := by
  classical
  set N : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Subgroup.normalizer (Work.L2F.pslSplitTorus F :
      Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) with hN
  have hle : Work.L2F.pslSplitTorus F ≤ N := Subgroup.le_normalizer
  set C : Subgroup ↥N := (Work.L2F.pslSplitTorus F).subgroupOf N with hC
  -- `π(T)` is cyclic, hence so is its copy inside the normalizer.
  have hcyc : IsCyclic ↥C :=
    (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hle)).mpr (pslSplitTorus_isCyclic F)
  -- the involution `w = π(z)`.
  have hWN : Work.PSL2.pslWeyl F ∈ N := by
    rw [hN]; exact pslWeyl_mem_normalizer F h2 h5
  set w : ↥N := ⟨Work.PSL2.pslWeyl F, hWN⟩ with hw
  have hw_notMem : w ∉ C := by
    rw [hC, Subgroup.mem_subgroupOf]
    exact pslWeyl_notMem F h2
  have hw_sq : w * w = 1 := by
    refine Subtype.ext ?_
    exact pslWeyl_mul_self F h2
  have hw_inv : ∀ c ∈ C, w * c * w⁻¹ = c⁻¹ := by
    intro c hc
    refine Subtype.ext ?_
    have hc' : (c : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ∈ Work.L2F.pslSplitTorus F :=
      (Subgroup.mem_subgroupOf.mp hc)
    exact pslWeyl_inverts F h2 _ hc'
  -- the coset computation: every element of `N` is in `C` or in `w C`.
  have hidx : C.index = 2 := by
    rw [Subgroup.index_eq_two_iff_exists_notMem_and]
    refine ⟨w, hw_notMem, ?_⟩
    intro b
    have hb : ((b : ↥N) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ∈
        (Subgroup.normalizer (Work.L2F.torus F :
          Set (Matrix.SpecialLinearGroup (Fin 2) F))).map (Work.PSL2.pslMap F) := by
      rw [← normalizer_pslSplitTorus_eq_map F h2]
      exact b.2
    obtain ⟨x, hxN, hx⟩ := Subgroup.mem_map.mp hb
    rcases (mem_normalizer_torus_iff F h2 h5 x).mp hxN with hxT | ⟨t, ht, hxt⟩
    · right
      rw [hC, Subgroup.mem_subgroupOf]
      rw [← hx]
      exact Subgroup.mem_map.mpr ⟨x, hxT, rfl⟩
    · left
      rw [hC, Subgroup.mem_subgroupOf]
      have hbw : ((b * w : ↥N) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) =
          Work.PSL2.pslWeyl F * Work.PSL2.pslMap F t * (Work.PSL2.pslWeyl F)⁻¹ := by
        have h1 : ((b * w : ↥N) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) =
            Work.PSL2.pslMap F (Work.L2F.z F * t) * Work.PSL2.pslWeyl F := by
          show ((b : ↥N) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) *
            Work.PSL2.pslWeyl F = _
          rw [show ((b : ↥N) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) =
            Work.PSL2.pslMap F x from hx.symm, hxt]
        rw [h1, map_mul]
        have hinv : (Work.PSL2.pslWeyl F)⁻¹ = Work.PSL2.pslWeyl F :=
          inv_eq_iff_mul_eq_one.mpr (pslWeyl_mul_self F h2)
        rw [hinv]
        rfl
      rw [hbw, pslWeyl_inverts F h2 _ (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩)]
      exact (Work.L2F.pslSplitTorus F).inv_mem (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩)
  have hcard : Nat.card ↥C = Nat.card (Work.L2F.pslSplitTorus F) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  obtain ⟨e⟩ := Work.L2F.Dihedral.mulEquiv_dihedral_of_cyclic_index_two C hcyc hidx
    ⟨w, hw_notMem, hw_sq, hw_inv⟩
  rw [← hcard]
  exact ⟨e⟩

end Work.L2F.PSL
