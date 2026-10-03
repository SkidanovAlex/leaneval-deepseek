import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.envelopeDefs
import Submission.Work.ORHughesFree.SkewLaurentSeriesInstances
import Submission.Work.ORHughesFree.SkewLaurentSeries.exists_injective_ringHom_skewMonoidAlgebra
import Submission.Work.Section6.skewLaurentSeries_mapRingHom

namespace Work.ORHughesFree.Section6

theorem exists_laurentEmbed {A P : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A] [Ring P]
    (fω : SkewMonoidAlgebra A (Multiplicative ℤ) →+* P) (Ψ : Work.ORHughesFree.SkewLaurentSeries A →+* P)
    (hΨ : ∀ p : SkewMonoidAlgebra A (Multiplicative ℤ),
      Ψ (Work.ORHughesFree.SkewLaurentSeries.toRingHom p) = fω p)
    (hΨinj : Function.Injective Ψ)
    (hfc : Function.Injective (fω.comp (SkewMonoidAlgebra.singleOneRingHom (G := Multiplicative ℤ))))
    (lam : Pˣ)
    (hlam : ((lam : Pˣ) : P) = fω (SkewMonoidAlgebra.single (Multiplicative.ofAdd 1) (1 : A)))
    (hact : ∀ (k : ℤ) (x : A),
      fω (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) ((Multiplicative.ofAdd k) • x)) =
        ((lam ^ k : Pˣ) : P) * fω (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) x) *
          (((lam ^ (-k) : Pˣ)) : P))
    (D : Subring A) (hD : ∀ (k : ℤ) (x : A), x ∈ D → (Multiplicative.ofAdd k) • x ∈ D) :
    let fc := fω.comp (SkewMonoidAlgebra.singleOneRingHom (G := Multiplicative ℤ))
    ∃ (inst : MulSemiringAction (Multiplicative ℤ) ↥(D.map fc)),
      (letI := inst
       ∃ (L : Work.ORHughesFree.SkewLaurentSeries ↥(D.map fc) →+* P),
        Function.Injective L ∧
        (∀ d : ↥(D.map fc), L (Work.ORHughesFree.skewLaurentCoeff ↥(D.map fc) d) = (d : P)) ∧
        L ((Work.ORHughesFree.skewLaurentSeriesT ↥(D.map fc) :
              (Work.ORHughesFree.SkewLaurentSeries ↥(D.map fc))ˣ) :
            Work.ORHughesFree.SkewLaurentSeries ↥(D.map fc)) = ((lam : Pˣ) : P)) := by
  classical
  dsimp only
  set fc := fω.comp (SkewMonoidAlgebra.singleOneRingHom (G := Multiplicative ℤ)) with hfc_def
  have hfc_inj : Function.Injective fc := hfc
  -- `hact` reformulated in terms of `fc`
  have hfc_smul : ∀ (k : ℤ) (x : A),
      fc ((Multiplicative.ofAdd k) • x) =
        ((lam ^ k : Pˣ) : P) * fc x * (((lam ^ (-k) : Pˣ)) : P) := by
    intro k x
    show fω (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) ((Multiplicative.ofAdd k) • x)) =
        ((lam ^ k : Pˣ) : P) *
          fω (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) x) *
            (((lam ^ (-k) : Pˣ)) : P)
    exact hact k x
  -- The monoid hom `ℤ → Pˣ`, `k ↦ lam ^ k`, promoted to `ConjAct Pˣ`.
  let ψ : Multiplicative ℤ →* ConjAct Pˣ :=
    { toFun := fun m => ConjAct.toConjAct (lam ^ (Multiplicative.toAdd m))
      map_one' := by simp
      map_mul' := by intro m n; rw [toAdd_mul, zpow_add]; rfl }
  have hψ_apply : ∀ m : Multiplicative ℤ,
      ConjAct.ofConjAct (ψ m) = lam ^ (Multiplicative.toAdd m) := by
    intro m
    show ConjAct.ofConjAct (ConjAct.toConjAct (lam ^ (Multiplicative.toAdd m))) = _
    rw [ConjAct.ofConjAct_toConjAct]
  -- The conjugation action of `lam` on the image of `D`.
  let conjSmul : Multiplicative ℤ → ↥(D.map fc) → ↥(D.map fc) :=
    fun m s => ⟨ψ m • (s : P), by
      obtain ⟨d, hdD, hds⟩ := Subring.mem_map.mp s.2
      refine Subring.mem_map.mpr
        ⟨(Multiplicative.ofAdd (Multiplicative.toAdd m)) • d, hD _ _ hdD, ?_⟩
      rw [ConjAct.units_smul_def, hψ_apply m, hfc_smul (Multiplicative.toAdd m) d, hds,
        zpow_neg]⟩
  have conjSmul_one : ∀ s : ↥(D.map fc), conjSmul 1 s = s := by
    intro s
    apply Subtype.ext
    show ψ 1 • (s : P) = (s : P)
    rw [map_one ψ, one_smul]
  have conjSmul_mul_smul : ∀ (m n : Multiplicative ℤ) (s : ↥(D.map fc)),
      conjSmul (m * n) s = conjSmul m (conjSmul n s) := by
    intro m n s
    apply Subtype.ext
    show ψ (m * n) • (s : P) = ψ m • (ψ n • (s : P))
    rw [map_mul ψ, mul_smul]
  have conjSmul_zero : ∀ m : Multiplicative ℤ, conjSmul m 0 = 0 := by
    intro m
    apply Subtype.ext
    show ψ m • ((0 : ↥(D.map fc)) : P) = (0 : P)
    rw [Subring.coe_zero, smul_zero]
  have conjSmul_add : ∀ (m : Multiplicative ℤ) (x y : ↥(D.map fc)),
      conjSmul m (x + y) = conjSmul m x + conjSmul m y := by
    intro m x y
    apply Subtype.ext
    show ψ m • ((x + y : ↥(D.map fc)) : P) = ψ m • (x : P) + ψ m • (y : P)
    rw [Subring.coe_add, smul_add]
  have conjSmul_mul : ∀ (m : Multiplicative ℤ) (x y : ↥(D.map fc)),
      conjSmul m (x * y) = conjSmul m x * conjSmul m y := by
    intro m x y
    apply Subtype.ext
    show ψ m • ((x * y : ↥(D.map fc)) : P) = ψ m • (x : P) * ψ m • (y : P)
    rw [Subring.coe_mul, MulSemiringAction.smul_mul]
  have conjSmul_one' : ∀ m : Multiplicative ℤ, conjSmul m 1 = 1 := by
    intro m
    apply Subtype.ext
    show ψ m • ((1 : ↥(D.map fc)) : P) = (1 : P)
    rw [Subring.coe_one, smul_one]
  let inst : MulSemiringAction (Multiplicative ℤ) ↥(D.map fc) :=
    { smul := conjSmul
      one_smul := conjSmul_one
      mul_smul := conjSmul_mul_smul
      smul_zero := conjSmul_zero
      smul_add := conjSmul_add
      smul_mul := conjSmul_mul
      smul_one := conjSmul_one' }
  refine ⟨inst, ?_⟩
  -- The inverse of `fc` restricted to `D`.
  let e : ↥D ≃+* ↥(D.map fc) := Subring.equivMapOfInjective D fc hfc_inj
  let liftS : ↥(D.map fc) →+* A := D.subtype.comp e.symm.toRingHom
  have liftS_inj : Function.Injective liftS := by
    intro x y h
    have h' : (e.symm x : ↥D) = e.symm y := by
      apply Subtype.ext
      exact h
    exact e.symm.injective h'
  have hfc_liftS : ∀ y : ↥(D.map fc), fc (liftS y) = (y : P) := by
    intro y
    have h := Subring.coe_equivMapOfInjective_apply D fc hfc_inj (e.symm y)
    rw [e.apply_symm_apply] at h
    exact h.symm
  -- `liftS` is equivariant for the two actions.
  have hlift : ∀ (k : ℤ) (x : ↥(D.map fc)),
      liftS ((Multiplicative.ofAdd k) • x) = (Multiplicative.ofAdd k) • liftS x := by
    intro k x
    apply hfc_inj
    rw [hfc_liftS ((Multiplicative.ofAdd k) • x), hfc_smul k (liftS x), hfc_liftS x]
    show ψ (Multiplicative.ofAdd k) • (x : P) =
      ((lam ^ k : Pˣ) : P) * (x : P) * (((lam ^ (-k) : Pˣ)) : P)
    rw [ConjAct.units_smul_def, hψ_apply (Multiplicative.ofAdd k), toAdd_ofAdd, zpow_neg]
  obtain ⟨G, hGapp, hGcoeff, hGinj⟩ := Work.Section6.skewLaurentSeries_mapRingHom liftS hlift
  -- `Ψ` on constant series.
  have toRingHom_single_apply : ∀ (k n : ℤ) (a : A),
      (SkewLaurentSeries.toRingHom (SkewMonoidAlgebra.single (Multiplicative.ofAdd k) a)).1 n
        = if n = k then a else 0 := by
    intro k n a
    change (SkewMonoidAlgebra.single (Multiplicative.ofAdd k) a).coeff
        (Multiplicative.ofAdd n) = if n = k then a else 0
    rw [SkewMonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases h : n = k
    · subst h; simp
    · rw [if_neg (fun hh => h (Multiplicative.ofAdd.injective hh).symm), if_neg h]
  have hcoeff_toRingHom : ∀ a : A,
      skewLaurentCoeff A a
        = SkewLaurentSeries.toRingHom (SkewMonoidAlgebra.single (Multiplicative.ofAdd 0) a) := by
    intro a
    apply Subtype.ext; funext n
    rw [show (skewLaurentCoeff A a).1 n = (if n = 0 then a else 0) from
        SkewLaurentSeries.coeff_apply a n,
      toRingHom_single_apply 0 n a]
  have hΨ_coeff : ∀ a : A, Ψ (skewLaurentCoeff A a) = fc a := by
    intro a
    rw [hcoeff_toRingHom a, hΨ, hfc_def]
    rfl
  -- `G` sends the variable `t` of `↥(D.map fc)((t;τ))` to the variable of `A((t;τ))`.
  have hGt : G (↑(skewLaurentSeriesT ↥(D.map fc)) : SkewLaurentSeries ↥(D.map fc))
      = SkewLaurentSeries.toRingHom (SkewMonoidAlgebra.single (Multiplicative.ofAdd 1) (1 : A)) := by
    apply Subtype.ext
    funext n
    rw [hGapp, toRingHom_single_apply 1 n (1 : A)]
    have htS : (↑(skewLaurentSeriesT ↥(D.map fc)) : SkewLaurentSeries ↥(D.map fc)).1 n
        = (if n = 1 then (1 : ↥(D.map fc)) else 0) := by
      rw [Work.ORHughesFree.skewLaurentSeriesT_coe]
      exact SkewLaurentSeries.t_apply n
    rw [htS]
    by_cases h : n = 1
    · simp [h, map_one]
    · simp [h, map_zero]
  refine ⟨Ψ.comp G, ?_, ?_, ?_⟩
  · intro a b h
    exact hGinj liftS_inj (hΨinj h)
  · intro d
    show Ψ (G (skewLaurentCoeff ↥(D.map fc) d)) = (d : P)
    rw [hGcoeff d, hΨ_coeff (liftS d), hfc_liftS d]
  · show Ψ (G (↑(skewLaurentSeriesT ↥(D.map fc)) : SkewLaurentSeries ↥(D.map fc)))
      = ((lam : Pˣ) : P)
    rw [hGt, hΨ, ← hlam]

end Work.ORHughesFree.Section6
