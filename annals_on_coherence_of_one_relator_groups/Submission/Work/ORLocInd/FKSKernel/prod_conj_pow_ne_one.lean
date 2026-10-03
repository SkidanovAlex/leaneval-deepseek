import Mathlib
import Submission.Work.OROneRel.letters_closure_iff
import Submission.Work.ORLocInd.FKSKernel.coprod_conj_prod_ne_one

/-!
# The syllable (normal form) computation for the free product `F(X \ {a}) * ⟨a⟩`

This file proves `Work.ORLocInd.FKSKernel.prod_conj_pow_ne_one`: if `K ≤ F(X)` is a subgroup all of
whose elements have reduced words avoiding the free generator `a`, and if `M` is a non-empty list of
pairs `(k, n) ∈ K × ℤ` with `n ≠ 0` and such that consecutive entries have distinct `K`-components,
then `∏ (k · a ^ n · k⁻¹) ≠ 1` in `F(X)`.

The proof factors the free group as the free product `F(X) = F({x // x ≠ a}) * ℤ` through the
homomorphism

`φ : F(X) →* F({x // x ≠ a}) ∗ ℤ`,  `of a ↦` (the generator of the `ℤ`-factor), other generators ↦
themselves in the first factor.

Each element of `K` lies in the first factor (`mem_range_freeGroup_lift_avoid`), and consecutive
`K`-components of `M` stay distinct in the free product (`injective_freeGroup_lift_avoid`).  The
free-product computation itself, the syllable argument, is
`Work.ORLocInd.FKSKernel.coprod_conj_prod_ne_one`.
-/

namespace Work.ORLocInd.FKSKernel

universe u

/-- If every letter of the canonical reduced word of `x : F(X)` is different from `a`, then `x` lies
in the image of the canonical map `F({x // x ≠ a}) →* F(X)`. -/
theorem mem_range_freeGroup_lift_avoid {X : Type u} [DecidableEq X] (a : X) (x : FreeGroup X)
    (hx : ∀ p ∈ x.toWord, p.1 ≠ a) :
    x ∈ (FreeGroup.lift (fun y : {x : X // x ≠ a} => FreeGroup.of (y : X))).range := by
  have h1 : FreeGroup.mk x.toWord ∈ Subgroup.closure (FreeGroup.of '' {b : X | b ≠ a}) :=
    Work.OROneRel.mk_mem_closure (T := {b : X | b ≠ a}) (L := x.toWord)
      (fun c b hb => hx (c, b) hb)
  rw [FreeGroup.mk_toWord] at h1
  have h2 : Subgroup.closure (FreeGroup.of '' {b : X | b ≠ a}) =
      (FreeGroup.lift (fun y : {x : X // x ≠ a} => FreeGroup.of (y : X))).range := by
    rw [FreeGroup.range_lift_eq_closure]
    congr 1
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨(b : X), b.2, rfl⟩
  rwa [h2] at h1

/-- The canonical map `F({x // x ≠ a}) →* F(X)` is injective. -/
theorem injective_freeGroup_lift_avoid {X : Type u} [DecidableEq X] (a : X) :
    Function.Injective (FreeGroup.lift (fun y : {x : X // x ≠ a} => FreeGroup.of (y : X))) := by
  let ψ : FreeGroup X →* FreeGroup {x : X // x ≠ a} :=
    FreeGroup.lift (fun x : X => if h : x = a then 1 else FreeGroup.of ⟨x, h⟩)
  have h1 : ∀ y : {x : X // x ≠ a}, ψ (FreeGroup.of (y : X)) = FreeGroup.of y := by
    intro y
    rw [FreeGroup.lift_apply_of]
    exact dif_neg y.2
  have hcomp : ψ.comp (FreeGroup.lift (fun y : {x : X // x ≠ a} => FreeGroup.of (y : X))) =
      MonoidHom.id (FreeGroup {x : X // x ≠ a}) := by
    apply FreeGroup.ext_hom
    intro y
    rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of, h1 y, MonoidHom.id_apply]
  exact Function.LeftInverse.injective (fun y => DFunLike.congr_fun hcomp y)

/-- `(ofAdd 1) ^ n = ofAdd n` in `Multiplicative (ULift ℤ)`. -/
private lemma ofAdd_one_zpow (n : ℤ) :
    ((Multiplicative.ofAdd (ULift.up (1 : ℤ)) : Multiplicative (ULift.{u,0} ℤ)) ^ n) =
      Multiplicative.ofAdd (ULift.up n) := by
  rw [← ofAdd_zsmul]
  congr 1
  apply ULift.ext
  rw [ULift.smul_down]
  simp

/-- The two factors of the free product `F({x // x ≠ a}) ∗ ℤ`, indexed by `ULift Bool` so that all
the factors live in the same universe as `X`. -/
@[reducible] private def MF (X : Type u) (a : X) : ULift.{u,0} Bool → Type u
  | ⟨false⟩ => FreeGroup {x : X // x ≠ a}
  | ⟨true⟩ => Multiplicative (ULift.{u,0} ℤ)

@[reducible] private instance instMF (X : Type u) (a : X) :
    ∀ b : ULift.{u,0} Bool, Group (MF X a b)
  | ⟨false⟩ => inferInstanceAs (Group (FreeGroup {x : X // x ≠ a}))
  | ⟨true⟩ => inferInstanceAs (Group (Multiplicative (ULift.{u,0} ℤ)))

theorem prod_conj_pow_ne_one {X : Type u} [DecidableEq X] (a : X) (K : Subgroup (FreeGroup X))
    (hK : ∀ k : K, ∀ p ∈ (k : FreeGroup X).toWord, p.1 ≠ a)
    (M : List (K × ℤ)) (hne : M ≠ []) (hnz : ∀ c ∈ M, c.2 ≠ 0)
    (hch : M.IsChain (fun x y => x.1 ≠ y.1)) :
    (M.map (fun c => (c.1 : FreeGroup X) * FreeGroup.of a ^ c.2 * (c.1 : FreeGroup X)⁻¹)).prod
      ≠ 1 := by
  classical
  let Y := {x : X // x ≠ a}
  let ιY : FreeGroup Y →* FreeGroup X := FreeGroup.lift (fun y : Y => FreeGroup.of (y : X))
  have hmem : ∀ k : K, (k : FreeGroup X) ∈ ιY.range :=
    fun k => mem_range_freeGroup_lift_avoid a _ (hK k)
  let y : K → FreeGroup Y := fun k => Classical.choose (hmem k)
  have hy : ∀ k : K, ιY (y k) = (k : FreeGroup X) := fun k => Classical.choose_spec (hmem k)
  have hy_inj : Function.Injective y := by
    intro k k' h
    apply Subtype.ext
    rw [← hy k, ← hy k', h]
  let t : Monoid.CoprodI (MF X a) :=
    Monoid.CoprodI.of (M := MF X a) (i := ULift.up true) (Multiplicative.ofAdd (ULift.up (1 : ℤ)))
  let φ : FreeGroup X →* Monoid.CoprodI (MF X a) :=
    FreeGroup.lift (fun x : X => if h : x = a then t
      else Monoid.CoprodI.of (M := MF X a) (i := ULift.up false) (FreeGroup.of ⟨x, h⟩))
  have hφa : φ (FreeGroup.of a) = t := by
    rw [FreeGroup.lift_apply_of]
    exact dif_pos rfl
  have hφι_ext : φ.comp ιY =
      (Monoid.CoprodI.of (M := MF X a) (i := ULift.up false) :
        FreeGroup {x : X // x ≠ a} →* Monoid.CoprodI (MF X a)) := by
    apply FreeGroup.ext_hom
    intro z
    show φ (ιY (FreeGroup.of z)) = _
    rw [show ιY (FreeGroup.of z) = FreeGroup.of (z : X) from FreeGroup.lift_apply_of]
    rw [FreeGroup.lift_apply_of]
    exact dif_neg z.2
  have hφι : ∀ z : FreeGroup Y, φ (ιY z) =
      Monoid.CoprodI.of (M := MF X a) (i := ULift.up false) z :=
    fun z => DFunLike.congr_fun hφι_ext z
  have hφk : ∀ k : K, φ (k : FreeGroup X) =
      Monoid.CoprodI.of (M := MF X a) (i := ULift.up false) (y k) := by
    intro k
    rw [← hy k]
    exact hφι (y k)
  let l : List (FreeGroup Y × Multiplicative (ULift.{u,0} ℤ)) :=
    M.map (fun c : K × ℤ => (y c.1, Multiplicative.ofAdd (ULift.up c.2)))
  have hl : l ≠ [] := by
    simpa [l] using hne
  have hne' : ∀ x ∈ l, x.2 ≠ 1 := by
    intro x hx
    simp only [l, List.mem_map] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    intro h
    have h' : (ULift.up c.2 : ULift.{u,0} ℤ) = 0 :=
      Multiplicative.ofAdd.injective (h.trans (ofAdd_zero (α := ULift.{u,0} ℤ)).symm)
    exact hnz c hc (by simpa using congrArg ULift.down h')
  have hch' : l.IsChain (fun x y => x.1 ≠ y.1) := by
    have h := List.isChain_map_of_isChain
      (R := fun x y : K × ℤ => x.1 ≠ y.1)
      (S := fun x y : FreeGroup Y × Multiplicative (ULift.{u,0} ℤ) => x.1 ≠ y.1)
      (f := fun c : K × ℤ => (y c.1, Multiplicative.ofAdd (ULift.up c.2)))
      (fun p q hpq hpq' => hpq (hy_inj hpq')) hch
    simpa [l] using h
  have hij : (ULift.up false : ULift.{u,0} Bool) ≠ ULift.up true := by
    intro h
    exact Bool.false_ne_true (congrArg ULift.down h)
  have hfp := coprod_conj_prod_ne_one (ι := ULift.{u,0} Bool) (MF X a)
    (i := ULift.up false) (j := ULift.up true) hij l hl hne' hch'
  have hkey : φ ((M.map (fun c : K × ℤ =>
        (c.1 : FreeGroup X) * FreeGroup.of a ^ c.2 * (c.1 : FreeGroup X)⁻¹)).prod) =
      (l.map (fun x : FreeGroup Y × Multiplicative (ULift.{u,0} ℤ) =>
        Monoid.CoprodI.of (M := MF X a) (i := ULift.up false) x.1 *
        Monoid.CoprodI.of (M := MF X a) (i := ULift.up true) x.2 *
        (Monoid.CoprodI.of (M := MF X a) (i := ULift.up false) x.1)⁻¹)).prod := by
    rw [map_list_prod]
    apply congrArg List.prod
    rw [show l = M.map (fun c : K × ℤ => (y c.1, Multiplicative.ofAdd (ULift.up c.2)))
      from rfl]
    simp only [List.map_map]
    apply List.map_congr_left
    intro c _
    show φ ((c.1 : FreeGroup X) * FreeGroup.of a ^ c.2 * (c.1 : FreeGroup X)⁻¹) =
      Monoid.CoprodI.of (M := MF X a) (i := ULift.up false) (y c.1) *
      Monoid.CoprodI.of (M := MF X a) (i := ULift.up true)
        (Multiplicative.ofAdd (ULift.up c.2)) *
      (Monoid.CoprodI.of (M := MF X a) (i := ULift.up false) (y c.1))⁻¹
    rw [map_mul, map_mul, map_zpow, map_inv, hφk c.1, hφa]
    have hinner : t ^ c.2 = Monoid.CoprodI.of (M := MF X a) (i := ULift.up true)
        (Multiplicative.ofAdd (ULift.up c.2)) := by
      rw [show t = Monoid.CoprodI.of (M := MF X a) (i := ULift.up true)
        (Multiplicative.ofAdd (ULift.up (1 : ℤ))) from rfl]
      rw [← map_zpow]
      exact congrArg _ (ofAdd_one_zpow c.2)
    rw [hinner]
  intro hprod
  rw [hprod, map_one] at hkey
  exact hfp hkey.symm

end Work.ORLocInd.FKSKernel
