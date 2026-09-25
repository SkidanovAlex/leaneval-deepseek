import Mathlib
import Submission.NK.LocalReciprocityLubinTate.LubinTate.ModuleAux
import Submission.NK.LocalReciprocityLubinTate.LubinTate.existsUnique_lubinTate_groupLaw

/-!
# The Lubin–Tate module: assembling the `R`-module structure

Milne, *Classical Field Theory*, §I.1 (Propositions I.2.12 and I.2.14).  Given a Lubin–Tate series
`f` for `(π,q)` over a commutative ring `A`, this file assembles the `A`-module structure
`a ↦ [a]` of `ModuleAux.lean` (`mulSeries`) with the Lubin–Tate group law of
`existsUnique_lubinTate_groupLaw` into a `NK.LocalReciprocityLubinTate.LubinTateModule`.

The group law is taken from the companion file (`LTgroupLaw`): the unique formal group law `F` with
`F ≡ X + Y (mod deg 2)` of which `f` is an endomorphism.  Its underlying series is identified with
the series `lawSeries` of `ModuleAux.lean` (`LTgroupLaw_coe_eq_lawSeries`), so that the module axioms
— which are stated with `subst1`/`subst2` against `lawSeries` — apply to it.
-/

open MvPowerSeries

namespace NK.LocalReciprocityLubinTate.LubinTate

universe u

noncomputable section

variable {A : Type u} [CommRing A] {π : A} {q : ℕ} {f : MvPowerSeries (Fin 1) A}

/-- **The Lubin–Tate formal group law** of `f` (Milne, *CFT*, Proposition I.2.12): the unique formal
group law `F` with `F ≡ X + Y (mod deg 2)` of which `f` is an endomorphism.  The companion file
`existsUnique_lubinTate_groupLaw` proves existence and uniqueness. -/
noncomputable def LTgroupLaw (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q)
    (hf : IsLubinTateSeries π q f) : FormalGroup A :=
  Classical.choose (existsUnique_lubinTate_groupLaw hπ hpow hf)

theorem LTgroupLaw_lin (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q)
    (hf : IsLubinTateSeries π q f) :
    CongruentModDegTwo (LTgroupLaw hπ hpow hf : MvPowerSeries (Fin 2) A)
      (MvPowerSeries.X 0 + MvPowerSeries.X 1) :=
  (Classical.choose_spec (existsUnique_lubinTate_groupLaw hπ hpow hf)).1.1

theorem LTgroupLaw_endo (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q)
    (hf : IsLubinTateSeries π q f) :
    IsEndoSeries (LTgroupLaw hπ hpow hf : MvPowerSeries (Fin 2) A) f :=
  (Classical.choose_spec (existsUnique_lubinTate_groupLaw hπ hpow hf)).1.2.1

theorem LTgroupLaw_isComm (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q)
    (hf : IsLubinTateSeries π q f) : (LTgroupLaw hπ hpow hf).IsComm :=
  (Classical.choose_spec (existsUnique_lubinTate_groupLaw hπ hpow hf)).1.2.2

/-- The underlying series of the chosen group law is `lawSeries`. -/
theorem LTgroupLaw_coe_eq_lawSeries (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q)
    (hf : IsLubinTateSeries π q f) :
    ((LTgroupLaw hπ hpow hf : FormalGroup A) : MvPowerSeries (Fin 2) A) = lawSeries hπ hpow hf := by
  refine lawSeries_unique hπ hpow hf (fun s hs => ?_) ?_
  · have h := LTgroupLaw_lin hπ hpow hf s (by omega)
    rw [h]
    exact (congrArg (fun g => MvPowerSeries.coeff s g) linForm2_one).symm
  · rw [gSub_two_eq]
    exact LTgroupLaw_endo hπ hpow hf

/-- The group law, coerced to a power series, agrees with the `lawSeries` of `ModuleAux.lean`
in every situation where one of them is used. -/
theorem coe_LTgroupLaw (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q)
    (hf : IsLubinTateSeries π q f) :
    (LTgroupLaw hπ hpow hf : MvPowerSeries (Fin 2) A) = lawSeries hπ hpow hf :=
  LTgroupLaw_coe_eq_lawSeries hπ hpow hf


/-! ### The module axioms -/

theorem mulSeries_zero {A : Type u} [CommRing A] {π : A} {q : ℕ}
    {f : MvPowerSeries (Fin 1) A}
    (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q) (hf : IsLubinTateSeries π q f) :
    mulSeries hπ hpow hf 0 = 0 := by
  refine (mulSeries_unique hπ hpow hf (c := 0) (φ := (0 : MvPowerSeries (Fin 1) A))
    (fun s _ => by rw [linForm1_zero, map_zero]) ?_).symm
  show subst1 (0 : MvPowerSeries (Fin 1) A) f
      = (0 : MvPowerSeries (Fin 1) A).subst (gSub 1 f)
  rw [subst1_zero_fam hf.1,
    show (0 : MvPowerSeries (Fin 1) A).subst (gSub 1 f)
      = subst1 f (0 : MvPowerSeries (Fin 1) A) by rw [subst1, gSub_one_eq],
    subst1_zero (hasSubst_vec1 hf.1)]

theorem mulSeries_one {A : Type u} [CommRing A] {π : A} {q : ℕ}
    {f : MvPowerSeries (Fin 1) A}
    (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q) (hf : IsLubinTateSeries π q f) :
    mulSeries hπ hpow hf 1 = MvPowerSeries.X 0 := by
  refine (mulSeries_unique hπ hpow hf (c := 1) (φ := MvPowerSeries.X (0 : Fin 1))
    (fun s _ => by rw [linForm1_one]) ?_).symm
  show subst1 (MvPowerSeries.X (0 : Fin 1)) f
      = (MvPowerSeries.X (0 : Fin 1)).subst (gSub 1 f)
  rw [subst1_X,
    show (MvPowerSeries.X (0 : Fin 1)).subst (gSub 1 f)
      = subst1 f (MvPowerSeries.X (0 : Fin 1)) by rw [subst1, gSub_one_eq],
    subst1_self (hasSubst_vec1 hf.1)]

theorem mulSeries_pi {A : Type u} [CommRing A] {π : A} {q : ℕ}
    {f : MvPowerSeries (Fin 1) A}
    (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q) (hf : IsLubinTateSeries π q f) :
    mulSeries hπ hpow hf π = f := by
  refine (mulSeries_unique hπ hpow hf (c := π) (φ := f)
    (fun s hs => (orderGe_sub_iff.mp (orderGe_two_sub_linForm1 hf)) s (by omega)) ?_).symm
  show subst1 f f = f.subst (gSub 1 f)
  rw [show f.subst (gSub 1 f) = subst1 f f by rw [subst1, gSub_one_eq]]

/-- **Milne, *CFT*, proof of Proposition I.2.14**: `[a]` is an endomorphism of the group law. -/
theorem mulSeries_endo_law' {A : Type u} [CommRing A] {π : A} {q : ℕ}
    {f : MvPowerSeries (Fin 1) A}
    (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q) (hf : IsLubinTateSeries π q f)
    (a : A) :
    subst1 (lawSeries hπ hpow hf) (mulSeries hπ hpow hf a)
      = subst2 (subst1 (MvPowerSeries.X 0) (mulSeries hπ hpow hf a))
          (subst1 (MvPowerSeries.X 1) (mulSeries hπ hpow hf a)) (lawSeries hπ hpow hf) := by
  set φ := mulSeries hπ hpow hf a with hφ
  set L := lawSeries hπ hpow hf with hL
  set A₀ := subst1 (MvPowerSeries.X (0 : Fin 2)) φ with hA₀
  set A₁ := subst1 (MvPowerSeries.X (1 : Fin 2)) φ with hA₁
  set B₀ := subst1 (MvPowerSeries.X (0 : Fin 2)) f with hB₀
  set B₁ := subst1 (MvPowerSeries.X (1 : Fin 2)) f with hB₁
  have hφcc : φ.constantCoeff = 0 := hφ.symm ▸ mulSeries_constantCoeff hπ hpow hf a
  have hLcc : L.constantCoeff = 0 := hL.symm ▸ lawSeries_constantCoeff hπ hpow hf
  have hφlin : OrderGe 2 (φ - linForm1 a) := hφ.symm ▸ mulSeries_orderGe_two hπ hpow hf a
  have hLlin : OrderGe 2 (L - linForm2 1 1) := hL.symm ▸ lawSeries_orderGe_two hπ hpow hf
  have hLendo : IsEndoSeries L f := hL.symm ▸ lawSeries_isEndoSeries hπ hpow hf
  have hφcomm : subst1 φ f = subst1 f φ := hφ.symm ▸ mulSeries_comm_subst1 hπ hpow hf a
  have hA₀cc : A₀.constantCoeff = 0 := hA₀.symm ▸ subst1_constantCoeff (by simp) hφcc
  have hA₁cc : A₁.constantCoeff = 0 := hA₁.symm ▸ subst1_constantCoeff (by simp) hφcc
  have hB₀cc : B₀.constantCoeff = 0 := hB₀.symm ▸ subst1_constantCoeff (by simp) hf.1
  have hB₁cc : B₁.constantCoeff = 0 := hB₁.symm ▸ subst1_constantCoeff (by simp) hf.1
  have hX₀c : (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) A).constantCoeff = 0 := by
    simp
  have hX₁c : (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) A).constantCoeff = 0 := by
    simp
  have hLendo' : subst1 L f = subst2 B₀ B₁ L := isEndoSeries_iff_subst1_subst2.mp hLendo
  -- `[a](F)` and `F([a],[a])` are both the unique two-variable solution for `aX + aY`
  obtain ⟨Ψ, -, hΨuniq⟩ := existsUnique_lawSeries2' hπ hpow hf a a
  have hUlin : OrderGe 2 (subst1 L φ - linForm2 a a) := by
    rw [orderGe_sub_iff]
    intro e he
    rw [coeff_subst_one_linear hφlin (OrderGe.of_constantCoeff hLcc) he,
      orderGe_sub_iff.mp hLlin e (by omega), ← coeff_linForm2_smul a 1 1 e]
    simp only [mul_one]
  have hVlin : OrderGe 2 (subst2 A₀ A₁ L - linForm2 a a) := by
    rw [orderGe_sub_iff]
    intro e he
    rw [coeff_subst_two_linear hLlin (OrderGe.of_constantCoeff hA₀cc)
      (OrderGe.of_constantCoeff hA₁cc) he, one_mul, one_mul]
    rw [show MvPowerSeries.coeff e A₀ = a * MvPowerSeries.coeff e (MvPowerSeries.X (0 : Fin 2)) by
        rw [hA₀]
        exact coeff_subst_one_linear hφlin (OrderGe.of_constantCoeff hX₀c) he,
      show MvPowerSeries.coeff e A₁ = a * MvPowerSeries.coeff e (MvPowerSeries.X (1 : Fin 2)) by
        rw [hA₁]
        exact coeff_subst_one_linear hφlin (OrderGe.of_constantCoeff hX₁c) he,
      MvPowerSeries.coeff_X, MvPowerSeries.coeff_X, coeff_linForm2]
  have hUeq : subst1 (subst1 L φ) f = subst2 B₀ B₁ (subst1 L φ) := by
    calc subst1 (subst1 L φ) f
        = subst1 L (subst1 φ f) :=
          (subst1_comp (hasSubst_vec1 hφcc) (hasSubst_vec1 hLcc)).symm
      _ = subst1 L (subst1 f φ) := by rw [hφcomm]
      _ = subst1 (subst1 L f) φ := subst1_comp (hasSubst_vec1 hf.1) (hasSubst_vec1 hLcc)
      _ = subst1 (subst2 B₀ B₁ L) φ := by rw [hLendo']
      _ = subst2 B₀ B₁ (subst1 L φ) :=
          (subst2_subst1_comp (hasSubst_vec1 hLcc) (hasSubst_vec2 hB₀cc hB₁cc)).symm
  have hAe₀ : subst2 A₀ A₁ B₀ = subst1 B₀ φ := by
    calc subst2 A₀ A₁ B₀ = subst2 A₀ A₁ (subst1 (MvPowerSeries.X (0 : Fin 2)) f) := by rw [hB₀]
      _ = subst1 (subst2 A₀ A₁ (MvPowerSeries.X (0 : Fin 2))) f :=
          subst2_subst1_comp (hasSubst_vec1 hX₀c) (hasSubst_vec2 hA₀cc hA₁cc)
      _ = subst1 A₀ f := by rw [subst2_X0 (hasSubst_vec2 hA₀cc hA₁cc)]
      _ = subst1 (subst1 (MvPowerSeries.X (0 : Fin 2)) φ) f := by rw [← hA₀]
      _ = subst1 (MvPowerSeries.X (0 : Fin 2)) (subst1 φ f) :=
          (subst1_comp (hasSubst_vec1 hφcc) (hasSubst_vec1 hX₀c)).symm
      _ = subst1 (MvPowerSeries.X (0 : Fin 2)) (subst1 f φ) := by rw [hφcomm]
      _ = subst1 (subst1 (MvPowerSeries.X (0 : Fin 2)) f) φ :=
          subst1_comp (hasSubst_vec1 hf.1) (hasSubst_vec1 hX₀c)
      _ = subst1 B₀ φ := by rw [← hB₀]
  have hAe₁ : subst2 A₀ A₁ B₁ = subst1 B₁ φ := by
    calc subst2 A₀ A₁ B₁ = subst2 A₀ A₁ (subst1 (MvPowerSeries.X (1 : Fin 2)) f) := by rw [hB₁]
      _ = subst1 (subst2 A₀ A₁ (MvPowerSeries.X (1 : Fin 2))) f :=
          subst2_subst1_comp (hasSubst_vec1 hX₁c) (hasSubst_vec2 hA₀cc hA₁cc)
      _ = subst1 A₁ f := by rw [subst2_X1 (hasSubst_vec2 hA₀cc hA₁cc)]
      _ = subst1 (subst1 (MvPowerSeries.X (1 : Fin 2)) φ) f := by rw [← hA₁]
      _ = subst1 (MvPowerSeries.X (1 : Fin 2)) (subst1 φ f) :=
          (subst1_comp (hasSubst_vec1 hφcc) (hasSubst_vec1 hX₁c)).symm
      _ = subst1 (MvPowerSeries.X (1 : Fin 2)) (subst1 f φ) := by rw [hφcomm]
      _ = subst1 (subst1 (MvPowerSeries.X (1 : Fin 2)) f) φ :=
          subst1_comp (hasSubst_vec1 hf.1) (hasSubst_vec1 hX₁c)
      _ = subst1 B₁ φ := by rw [← hB₁]
  have hBe₀ : subst2 B₀ B₁ A₀ = subst1 B₀ φ := by
    calc subst2 B₀ B₁ A₀ = subst2 B₀ B₁ (subst1 (MvPowerSeries.X (0 : Fin 2)) φ) := by rw [hA₀]
      _ = subst1 (subst2 B₀ B₁ (MvPowerSeries.X (0 : Fin 2))) φ :=
          subst2_subst1_comp (hasSubst_vec1 hX₀c) (hasSubst_vec2 hB₀cc hB₁cc)
      _ = subst1 B₀ φ := by rw [subst2_X0 (hasSubst_vec2 hB₀cc hB₁cc)]
  have hBe₁ : subst2 B₀ B₁ A₁ = subst1 B₁ φ := by
    calc subst2 B₀ B₁ A₁ = subst2 B₀ B₁ (subst1 (MvPowerSeries.X (1 : Fin 2)) φ) := by rw [hA₁]
      _ = subst1 (subst2 B₀ B₁ (MvPowerSeries.X (1 : Fin 2))) φ :=
          subst2_subst1_comp (hasSubst_vec1 hX₁c) (hasSubst_vec2 hB₀cc hB₁cc)
      _ = subst1 B₁ φ := by rw [subst2_X1 (hasSubst_vec2 hB₀cc hB₁cc)]
  have hVeq : subst1 (subst2 A₀ A₁ L) f = subst2 B₀ B₁ (subst2 A₀ A₁ L) := by
    have h₁ : subst1 (subst2 A₀ A₁ L) f = subst2 (subst1 B₀ φ) (subst1 B₁ φ) L := by
      calc subst1 (subst2 A₀ A₁ L) f = subst2 A₀ A₁ (subst1 L f) :=
            (subst2_subst1_comp (hasSubst_vec1 hLcc) (hasSubst_vec2 hA₀cc hA₁cc)).symm
        _ = subst2 A₀ A₁ (subst2 B₀ B₁ L) := by rw [hLendo']
        _ = subst2 (subst2 A₀ A₁ B₀) (subst2 A₀ A₁ B₁) L :=
            subst2_subst2_comp (hasSubst_vec2 hB₀cc hB₁cc) (hasSubst_vec2 hA₀cc hA₁cc)
        _ = subst2 (subst1 B₀ φ) (subst1 B₁ φ) L := by
            rw [hAe₀, hAe₁]
    have h₂ : subst2 B₀ B₁ (subst2 A₀ A₁ L) = subst2 (subst1 B₀ φ) (subst1 B₁ φ) L := by
      calc subst2 B₀ B₁ (subst2 A₀ A₁ L)
          = subst2 (subst2 B₀ B₁ A₀) (subst2 B₀ B₁ A₁) L :=
            subst2_subst2_comp (hasSubst_vec2 hA₀cc hA₁cc) (hasSubst_vec2 hB₀cc hB₁cc)
        _ = subst2 (subst1 B₀ φ) (subst1 B₁ φ) L := by rw [hBe₀, hBe₁]
    rw [h₁, h₂]
  have hU : subst1 L φ = Ψ := hΨuniq _
    ⟨fun s hs => (orderGe_sub_iff.mp hUlin) s (by omega), hUeq⟩
  have hV : subst2 A₀ A₁ L = Ψ := hΨuniq _
    ⟨fun s hs => (orderGe_sub_iff.mp hVlin) s (by omega), hVeq⟩
  rw [hU, hV]

/-- **Milne, *CFT*, proof of Proposition I.2.14**: `[a+b] = F([a],[b])`. -/
theorem mulSeries_add' {A : Type u} [CommRing A] {π : A} {q : ℕ} {f : MvPowerSeries (Fin 1) A}
    (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q) (hf : IsLubinTateSeries π q f)
    (a b : A) :
    mulSeries hπ hpow hf (a + b)
      = subst2 (mulSeries hπ hpow hf a) (mulSeries hπ hpow hf b) (lawSeries hπ hpow hf) := by
  set φ := mulSeries hπ hpow hf a with hφ
  set ψ := mulSeries hπ hpow hf b with hψ
  set L := lawSeries hπ hpow hf with hL
  have hφcc : φ.constantCoeff = 0 := hφ.symm ▸ mulSeries_constantCoeff hπ hpow hf a
  have hψcc : ψ.constantCoeff = 0 := hψ.symm ▸ mulSeries_constantCoeff hπ hpow hf b
  have hLcc : L.constantCoeff = 0 := hL.symm ▸ lawSeries_constantCoeff hπ hpow hf
  have hφlin : OrderGe 2 (φ - linForm1 a) := hφ.symm ▸ mulSeries_orderGe_two hπ hpow hf a
  have hψlin : OrderGe 2 (ψ - linForm1 b) := hψ.symm ▸ mulSeries_orderGe_two hπ hpow hf b
  have hLlin : OrderGe 2 (L - linForm2 1 1) := hL.symm ▸ lawSeries_orderGe_two hπ hpow hf
  have hLendo : IsEndoSeries L f := hL.symm ▸ lawSeries_isEndoSeries hπ hpow hf
  have hφcomm : subst1 φ f = subst1 f φ := hφ.symm ▸ mulSeries_comm_subst1 hπ hpow hf a
  have hψcomm : subst1 ψ f = subst1 f ψ := hψ.symm ▸ mulSeries_comm_subst1 hπ hpow hf b
  have hX₀c : (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) A).constantCoeff = 0 := by
    simp
  have hX₁c : (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) A).constantCoeff = 0 := by
    simp
  have hLendo' : subst1 L f = subst2 (subst1 (MvPowerSeries.X 0) f)
      (subst1 (MvPowerSeries.X 1) f) L := isEndoSeries_iff_subst1_subst2.mp hLendo
  refine (mulSeries_unique'' hπ hpow hf (c := a + b) (φ := subst2 φ ψ L) ?_ ?_).symm
  · rw [orderGe_sub_iff]
    intro e he
    rw [coeff_subst_two_linear hLlin (OrderGe.of_constantCoeff hφcc)
        (OrderGe.of_constantCoeff hψcc) he, one_mul, one_mul,
      orderGe_sub_iff.mp hφlin e (by omega), orderGe_sub_iff.mp hψlin e (by omega),
      ← coeff_linForm1_add a b e]
  · have h₁ : subst1 (subst2 φ ψ L) f = subst2 (subst1 f φ) (subst1 f ψ) L := by
      calc subst1 (subst2 φ ψ L) f = subst2 φ ψ (subst1 L f) :=
            (subst2_subst1_comp (hasSubst_vec1 hLcc) (hasSubst_vec2 hφcc hψcc)).symm
        _ = subst2 φ ψ (subst2 (subst1 (MvPowerSeries.X 0) f)
              (subst1 (MvPowerSeries.X 1) f) L) := by rw [hLendo']
        _ = subst2 (subst2 φ ψ (subst1 (MvPowerSeries.X 0) f))
              (subst2 φ ψ (subst1 (MvPowerSeries.X 1) f)) L :=
            subst2_subst2_comp (hasSubst_vec2 (subst1_constantCoeff (by simp) hf.1)
              (subst1_constantCoeff (by simp) hf.1)) (hasSubst_vec2 hφcc hψcc)
        _ = subst2 (subst1 f φ) (subst1 f ψ) L := by
            have e₀ : subst2 φ ψ (subst1 (MvPowerSeries.X (0 : Fin 2)) f)
                = subst1 f φ := by
              calc subst2 φ ψ (subst1 (MvPowerSeries.X (0 : Fin 2)) f)
                  = subst1 (subst2 φ ψ (MvPowerSeries.X (0 : Fin 2))) f :=
                    subst2_subst1_comp (hasSubst_vec1 hX₀c) (hasSubst_vec2 hφcc hψcc)
                _ = subst1 φ f := by
                    rw [subst2_X0 (hasSubst_vec2 hφcc hψcc)]
                _ = subst1 f φ := hφcomm
            have e₁ : subst2 φ ψ (subst1 (MvPowerSeries.X (1 : Fin 2)) f)
                = subst1 f ψ := by
              calc subst2 φ ψ (subst1 (MvPowerSeries.X (1 : Fin 2)) f)
                  = subst1 (subst2 φ ψ (MvPowerSeries.X (1 : Fin 2))) f :=
                    subst2_subst1_comp (hasSubst_vec1 hX₁c) (hasSubst_vec2 hφcc hψcc)
                _ = subst1 ψ f := by
                    rw [subst2_X1 (hasSubst_vec2 hφcc hψcc)]
                _ = subst1 f ψ := hψcomm
            rw [e₀, e₁]
    have h₂ : subst1 f (subst2 φ ψ L) = subst2 (subst1 f φ) (subst1 f ψ) L :=
      subst1_subst2_comp (hasSubst_vec2 hφcc hψcc) (hasSubst_vec1 hf.1)
    rw [h₁, h₂]

/-- **Milne, *CFT*, proof of Proposition I.2.14**: `[ab] = [a]∘[b]`. -/
theorem mulSeries_mul' {A : Type u} [CommRing A] {π : A} {q : ℕ} {f : MvPowerSeries (Fin 1) A}
    (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q) (hf : IsLubinTateSeries π q f)
    (a b : A) :
    mulSeries hπ hpow hf (a * b)
      = subst1 (mulSeries hπ hpow hf b) (mulSeries hπ hpow hf a) := by
  set φ := mulSeries hπ hpow hf a with hφ
  set ψ := mulSeries hπ hpow hf b with hψ
  have hφcc : φ.constantCoeff = 0 := hφ.symm ▸ mulSeries_constantCoeff hπ hpow hf a
  have hψcc : ψ.constantCoeff = 0 := hψ.symm ▸ mulSeries_constantCoeff hπ hpow hf b
  have hφlin : OrderGe 2 (φ - linForm1 a) := hφ.symm ▸ mulSeries_orderGe_two hπ hpow hf a
  have hψlin : OrderGe 2 (ψ - linForm1 b) := hψ.symm ▸ mulSeries_orderGe_two hπ hpow hf b
  have hφcomm : subst1 φ f = subst1 f φ := hφ.symm ▸ mulSeries_comm_subst1 hπ hpow hf a
  have hψcomm : subst1 ψ f = subst1 f ψ := hψ.symm ▸ mulSeries_comm_subst1 hπ hpow hf b
  refine (mulSeries_unique'' hπ hpow hf (c := a * b) (φ := subst1 ψ φ) ?_ ?_).symm
  · rw [orderGe_sub_iff]
    intro e he
    rw [coeff_subst_one_linear hφlin (OrderGe.of_constantCoeff hψcc) he,
      orderGe_sub_iff.mp hψlin e (by omega), coeff_linForm1, coeff_linForm1, ← mul_assoc]
  · calc subst1 (subst1 ψ φ) f
        = subst1 ψ (subst1 φ f) := (subst1_comp (hasSubst_vec1 hφcc) (hasSubst_vec1 hψcc)).symm
      _ = subst1 ψ (subst1 f φ) := by rw [hφcomm]
      _ = subst1 (subst1 ψ f) φ := subst1_comp (hasSubst_vec1 hf.1) (hasSubst_vec1 hψcc)
      _ = subst1 (subst1 f ψ) φ := by rw [hψcomm]
      _ = subst1 f (subst1 ψ φ) := (subst1_comp (hasSubst_vec1 hψcc) (hasSubst_vec1 hf.1)).symm


/-! ### The Lubin–Tate module -/

/-- **The Lubin–Tate module** of a Lubin–Tate series `f` (Milne, *CFT*, Propositions I.2.12 and
I.2.14): the Lubin–Tate formal group law of `f`, together with the `A`-module structure
`a ↦ [a] = mulSeries a`.  The group law is the one provided by `existsUnique_lubinTate_groupLaw`;
the module axioms are the lemmas of this file. -/
noncomputable def ltModule (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q)
    (hf : IsLubinTateSeries π q f) : LubinTateModule A π q where
  toLaw :=
    { law := LTgroupLaw hπ hpow hf
      comm := LTgroupLaw_isComm hπ hpow hf
      piEndo := f
      piEndo_zero := hf.1
      piEndo_linear := fun s hs => (orderGe_sub_iff.mp (orderGe_two_sub_linForm1 hf)) s hs
      piEndo_endo := LTgroupLaw_endo hπ hpow hf }
  action := fun a => mulSeries hπ hpow hf a
  action_one := mulSeries_one hπ hpow hf
  action_add := fun a b => by
    rw [show (LTgroupLaw hπ hpow hf : MvPowerSeries (Fin 2) A) = lawSeries hπ hpow hf from
      LTgroupLaw_coe_eq_lawSeries hπ hpow hf]
    exact mulSeries_add' hπ hpow hf a b
  action_mul := fun a b => mulSeries_mul' hπ hpow hf a b
  action_end := fun a => by
    rw [show (LTgroupLaw hπ hpow hf : MvPowerSeries (Fin 2) A) = lawSeries hπ hpow hf from
      LTgroupLaw_coe_eq_lawSeries hπ hpow hf]
    exact mulSeries_endo_law' hπ hpow hf a
  action_linear := fun a s hs => (orderGe_sub_iff.mp (mulSeries_orderGe_two hπ hpow hf a)) s hs
  action_pi := mulSeries_pi hπ hpow hf

/-- The `π`-multiplication of the Lubin–Tate module of `f` is `f` itself. -/
theorem ltModule_piEndo (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q)
    (hf : IsLubinTateSeries π q f) : (ltModule hπ hpow hf).toLaw.piEndo = f := rfl

/-- **Existence of the Lubin–Tate module**: for a Lubin–Tate series `f` for `(π,q)` there is a
Lubin–Tate module whose `π`-multiplication is `f` (Milne, *CFT*, §I.1). -/
theorem nonempty_lubinTateModule' (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q)
    (hf : IsLubinTateSeries π q f) :
    ∃ M : LubinTateModule A π q, M.toLaw.piEndo = f :=
  ⟨ltModule hπ hpow hf, ltModule_piEndo hπ hpow hf⟩

end

end NK.LocalReciprocityLubinTate.LubinTate
