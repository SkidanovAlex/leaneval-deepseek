import Mathlib
import Submission.Work.Hering.HardCore.Defs
import Submission.Work.Hering.HardCore.isSuzuki_of_config
import Submission.Work.Higman.Class
import Submission.Work.Hering.AppVIII.Defs
import Submission.Work.Hering.GL32.AppIXDefs
import Submission.Work.Hering.GL32.singer_of_exp_two
import Submission.Work.Hering.HardCore.q2_aut_solvable
import Submission.Work.Hering.GL32.gl32_not_solvable_v2
import Submission.Work.Hering.AppVIII.cTypeP1_top
import Submission.Work.Hering.HardCore.cTheta_eq_thetaC
import Submission.Work.Hering.HardCore.noIsotropic_B3
import Submission.Work.Hering.HardCore.not_isSolvable_mulAut_normal
import Submission.Work.Hering.HardCore.q3_module
import Submission.Work.Hering.HardCore.q3_suzuki_sixtyfour
import Submission.Work.Hering.HardCore.q3_nonabelian_false
import Submission.Work.Hering.HardCore.aut_transitive

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.Hering.HardCore

open LeanEval.GroupTheory.Defs

/-- In the configuration, `V` has exponent two, hence is abelian. -/
private lemma V_comm' {G : Type} [Group G] (V : Subgroup G) (hexp : ∀ x ∈ V, x * x = 1)
    {x y : G} (hx : x ∈ V) (hy : y ∈ V) : x * y = y * x := by
  have hx1 : x * x = 1 := hexp x hx
  have hy1 : y * y = 1 := hexp y hy
  have hxy : (x * y) * (x * y) = 1 := hexp (x * y) (V.mul_mem hx hy)
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx1
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy1
  have h2 : x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy).symm
  rw [mul_inv_rev, hxinv, hyinv] at h2
  exact h2

/-- In the configuration, `V ≤ C_G(V) = C`. -/
private lemma V_le_C' {G : Type} [Group G] (V C : Subgroup G)
    (hC : C = Subgroup.centralizer ((V : Set G))) (hexp : ∀ x ∈ V, x * x = 1) : V ≤ C := by
  intro x hx
  rw [hC, Subgroup.mem_centralizer_iff]
  intro v hv
  exact V_comm' V hexp hv hx

/-- In the configuration, `Nat.card (Z(C)) = 8` (`Z(C) = Ω₁(C) = V`). -/
private lemma center_card_eq {G : Type} [Group G] (V C : Subgroup G)
    (hcard : Nat.card V = 8) (hexp : ∀ x ∈ V, x * x = 1)
    (hC : C = Subgroup.centralizer ((V : Set G)))
    (hinv : ∀ x ∈ C, orderOf x = 2 → x ∈ V)
    (hcenter : ∀ z : ↥C, z ∈ Subgroup.center ↥C ↔ z ^ 2 = 1) :
    Nat.card ↥(Subgroup.center ↥C) = 8 := by
  have hiff : ∀ z : ↥C, z ∈ Subgroup.center ↥C ↔ ((z : G) ∈ V) := by
    intro z
    rw [hcenter]
    constructor
    · intro hz
      have hz2 : (z : G) ^ 2 = 1 := by
        have h := congrArg (fun t : ↥C => (t : G)) hz
        simpa using h
      rcases eq_or_ne (z : G) 1 with h1 | h1
      · rw [h1]; exact V.one_mem
      · exact hinv (z : G) z.2 (orderOf_eq_prime hz2 h1)
    · intro hz
      show z ^ 2 = 1
      have hz2 : (z : G) * (z : G) = 1 := hexp (z : G) hz
      exact Subtype.ext (by simpa [pow_two] using hz2)
  have hVleC : V ≤ C := V_le_C' V C hC hexp
  have hbij : Nat.card ↥(Subgroup.center ↥C) = Nat.card ↥V :=
    Nat.card_congr
      { toFun := fun z => ⟨((z : ↥C) : G), (hiff (z : ↥C)).mp z.2⟩
        invFun := fun v => ⟨⟨(v : G), hVleC v.2⟩, (hiff ⟨(v : G), hVleC v.2⟩).mpr
          (show ((⟨(v : G), hVleC v.2⟩ : ↥C) : G) ∈ V from v.2)⟩
        left_inv := by rintro ⟨z, hz⟩; rfl
        right_inv := by rintro ⟨v, hv⟩; rfl }
  rw [hbij, hcard]

/-- **The reduction.**  In the configuration of Peterfalvi I §3–§4, `C = C_G(V)` is a
Suzuki 2-group with `Z(C) = Ω₁(C) = V`, and `Aut(C)` is not solvable. -/
private lemma reduction {G : Type} [Group G] [Finite G]
    (V C : Subgroup G) (hV : V.Normal) (hcard : Nat.card V = 8)
    (hexp : ∀ x ∈ V, x * x = 1) (hC : C = Subgroup.centralizer ((V : Set G)))
    (hC2 : IsPGroup 2 ↥C) (hinv : ∀ x ∈ C, orderOf x = 2 → x ∈ V) (hAut : ActsAsAut V hV)
    (hnotab : ¬ ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    (hHig : Work.Higman.HigmanClassProp) :
    Work.Hering.IsSuzukiTwoGroup ↥C ∧
      Nat.card ↥(Subgroup.center ↥C) = 8 ∧
      ¬ Group.IsSolvable (MulAut ↥C) := by
  have hVcomm : ∀ x y : ↥V, x * y = y * x := by
    intro x y
    exact Subtype.ext (V_comm' V hexp x.2 y.2)
  have hVexp : ∀ x : ↥V, x * x = 1 := by
    intro x
    exact Subtype.ext (hexp x x.2)
  obtain ⟨ξ, hξord, hξtrans⟩ :=
    Work.Hering.GL32.singer_of_exp_two hVcomm hVexp hcard
  have hSinger : ∃ ξ : MulAut ↥V, orderOf ξ = 7 ∧
      ∀ a b : ↥V, (a : G) ≠ 1 → (b : G) ≠ 1 → ∃ k : ℕ, (ξ ^ k) a = b := by
    refine ⟨ξ, hξord, ?_⟩
    intro a b ha hb
    refine hξtrans a b ?_ ?_
    · intro h; exact ha (by rw [h]; rfl)
    · intro h; exact hb (by rw [h]; rfl)
  have hSuz : Work.Hering.IsSuzukiTwoGroup ↥C :=
    isSuzuki_of_config V C hV hcard hexp hC hC2 hinv hAut hnotab hSinger
  obtain ⟨hcenter, -, -, -, -⟩ := hHig.1 ↥C hSuz
  have hZcard := center_card_eq V C hcard hexp hC hinv hcenter
  -- `Aut(C)` is not solvable: `G/C ≅ Aut(V)` is non-solvable and is a quotient of a subgroup
  -- of `Aut(C)`.
  have hW3ns : ¬ Group.IsSolvable (MulAut (Multiplicative (Fin 3 → ZMod 2))) :=
    Work.Hering.GL32.gl32_not_solvable_v2
  have hVns : ¬ Group.IsSolvable (MulAut ↥V) := by
    obtain ⟨e⟩ := Work.Hering.Step5.iso_fin3 hcard hVexp
    intro hsol
    haveI := hsol
    exact hW3ns (Group.isSolvable_of_surjective (f := (MulAut.congr e).toMonoidHom)
      (MulAut.congr e).surjective)
  have hψ : ∀ φ : MulAut ↥V, ∃ g : G, ∀ v : ↥V,
      φ v = (MulAut.conjNormal g) v := by
    intro φ
    obtain ⟨g, hg⟩ := hAut φ
    exact ⟨g, fun v => Subtype.ext (by
      rw [MulAut.conjNormal_apply]
      exact congrArg Subtype.val (hg v))⟩
  have hsurj : Function.Surjective (MulAut.conjNormal (H := V) : G →* MulAut ↥V) := by
    intro φ; obtain ⟨g, hg⟩ := hψ φ
    exact ⟨g, MulEquiv.ext (fun v => (hg v).symm)⟩
  have hψker : (MulAut.conjNormal (H := V) : G →* MulAut ↥V).ker = C := by
    ext g
    rw [MonoidHom.mem_ker, hC, Subgroup.mem_centralizer_iff]
    constructor
    · intro hg v hv
      have h1 : (MulAut.conjNormal g : MulAut ↥V) ⟨v, hv⟩ = ⟨v, hv⟩ := by rw [hg]; rfl
      have h2 := congrArg (fun w : ↥V => (w : G)) h1
      rw [MulAut.conjNormal_apply] at h2
      calc v * g = (g * v * g⁻¹) * g := by rw [h2]
        _ = g * v := by group
    · intro hg
      apply MulEquiv.ext
      intro v
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      show g * (v : G) * g⁻¹ = (v : G)
      calc g * (v : G) * g⁻¹ = ((v : G) * g) * g⁻¹ := by rw [hg (v : G) v.2]
        _ = (v : G) := by group
  have hCns : ¬ Group.IsSolvable (MulAut ↥C) := by
    intro hsol
    haveI := hsol
    haveI hCn : C.Normal := hC.symm ▸ Subgroup.normal_centralizer
    set ρ : G →* MulAut ↥C := MulAut.conjNormal with hρdef
    have hker_le : ρ.ker ≤ C := by
      intro g hg
      rw [MonoidHom.mem_ker] at hg
      rw [hC, Subgroup.mem_centralizer_iff]
      intro v hv
      have hvC : v ∈ C := V_le_C' V C hC hexp hv
      have h1 : ρ g ⟨v, hvC⟩ = ⟨v, hvC⟩ := by rw [hg]; rfl
      have h2 : g * v * g⁻¹ = v := by
        have := congrArg (fun w : ↥C => (w : G)) h1
        simpa [hρdef, MulAut.conjNormal_apply] using this
      calc v * g = (g * v * g⁻¹) * g := by rw [h2]
        _ = g * v := by group
    have hquot : Group.IsSolvable (G ⧸ ρ.ker) :=
      Group.isSolvable_of_surjective
        (f := (QuotientGroup.quotientKerEquivRange ρ).symm.toMonoidHom)
        (QuotientGroup.quotientKerEquivRange ρ).symm.surjective
    have : Group.IsSolvable (MulAut ↥V) :=
      Group.isSolvable_of_surjective
        (f := QuotientGroup.lift ρ.ker (MulAut.conjNormal (H := V))
          (by rw [hψker]; exact hker_le)) (by
          intro φ
          obtain ⟨g, hg⟩ := hsurj φ
          exact ⟨QuotientGroup.mk g, by
            show QuotientGroup.lift ρ.ker (MulAut.conjNormal (H := V)) _ (QuotientGroup.mk g) = φ
            rw [QuotientGroup.lift_mk]
            exact hg⟩)
    exact hVns this
  exact ⟨hSuz, hZcard, hCns⟩

/-- A group whose multiplication is given by the two-step law of a biadditive cocycle `b` is
isomorphic to `TwoStep A Z b`. -/
private def twoStepIso {P : Type*} [Group P] {A Z : Type*} [AddCommGroup A] [AddCommGroup Z]
    [Work.Higman.AddExpTwo A] [Work.Higman.AddExpTwo Z] (b : A → A → Z) [Work.Higman.Biadd b]
    (e : P ≃ A × Z)
    (hlaw : ∀ x y : P,
      e (x * y) = ((e x).1 + (e y).1, (e x).2 + (e y).2 + b (e x).1 (e y).1)) :
    P ≃* Work.Higman.TwoStep A Z b where
  toFun p := ⟨(e p).1, (e p).2⟩
  invFun t := e.symm (t.fst, t.snd)
  left_inv p := by simp
  right_inv t := by cases t with | mk f s => simp
  map_mul' x y := by
    apply Work.Higman.TwoStep.ext_iff
    · simp only [Work.Higman.TwoStep.fst_mul, hlaw x y]
    · simp only [Work.Higman.TwoStep.snd_mul, hlaw x y]

/-- In the configuration, the two-step model of `C` has anisotropic squaring form. -/
private lemma bAniso {G : Type} [Group G] [Finite G] (V C : Subgroup G)
    (hexp : ∀ x ∈ V, x * x = 1)
    {A Z : Type*} [AddCommGroup A] [AddCommGroup Z] [Work.Higman.AddExpTwo A]
    [Work.Higman.AddExpTwo Z] [Finite A] [Finite Z] (b : A → A → Z) [Work.Higman.Biadd b]
    (φ : ↥C ≃* Work.Higman.TwoStep A Z b)
    (hZV : ∀ z : ↥C, z ∈ Subgroup.center ↥C ↔ ((z : G) ∈ V))
    (hZc : Nat.card ↥(Subgroup.center ↥C) = 8) (hZcard : Nat.card Z = 8)
    (hinv : ∀ x ∈ C, orderOf x = 2 → x ∈ V) :
    ∀ u : A, b u u = 0 → u = 0 := by
  intro u hu
  -- `Z(TwoStep A Z b) = kerFst`
  have hker : Nat.card ↥(Work.Higman.TwoStep.kerFst (A := A) (Z := Z) (b := b)) = 8 := by
    have hbij : Nat.card ↥(Work.Higman.TwoStep.kerFst (A := A) (Z := Z) (b := b)) =
        Nat.card Z :=
      Nat.card_congr
        { toFun := fun x => (x : Work.Higman.TwoStep A Z b).snd
          invFun := fun z => ⟨⟨0, z⟩, rfl⟩
          left_inv := by
            intro x
            apply Subtype.ext
            exact Work.Higman.TwoStep.ext_iff (Work.Higman.TwoStep.mem_kerFst.mp x.2).symm rfl
          right_inv := by intro z; rfl }
    rw [hbij, hZcard]
  have hcen : Nat.card ↥(Subgroup.center (Work.Higman.TwoStep A Z b)) = 8 := by
    have h1 : Nat.card ↥(Subgroup.center (Work.Higman.TwoStep A Z b)) =
        Nat.card ↥(Subgroup.center ↥C) := by
      rw [← Subgroup.map_center_eq φ]
      exact Nat.card_congr ((Subgroup.equivMapOfInjective (Subgroup.center ↥C)
        (φ : ↥C →* Work.Higman.TwoStep A Z b) φ.injective).symm.toEquiv)
    rw [h1, hZc]
  have hcenter_eq : Subgroup.center (Work.Higman.TwoStep A Z b) = Work.Higman.TwoStep.kerFst :=
    (Subgroup.eq_of_le_of_card_ge (H := Work.Higman.TwoStep.kerFst (A := A) (Z := Z) (b := b))
      (K := Subgroup.center (Work.Higman.TwoStep A Z b))
      Work.Higman.TwoStep.kerFst_le_center (by rw [hker, hcen])).symm
  -- the element `⟨u,0⟩` has square `1`, so `φ.symm ⟨u,0⟩` has order dividing two
  let x : Work.Higman.TwoStep A Z b := ⟨u, 0⟩
  have hx2 : x ^ 2 = 1 := by
    rw [Work.Higman.TwoStep.sq_eq_one_iff]
    exact hu
  let c : ↥C := φ.symm x
  have hc2 : c ^ 2 = 1 := by
    have := congrArg (fun t : Work.Higman.TwoStep A Z b => φ.symm t) hx2
    simpa [c, x] using this
  rcases eq_or_ne c 1 with hc1 | hcne
  · have : x = 1 := by
      have := congrArg φ hc1
      simpa [c, x] using this
    have : u = 0 := by simpa [x] using congrArg (fun t : Work.Higman.TwoStep A Z b => t.fst) this
    exact this
  · have hord : orderOf c = 2 := by
      have hd : orderOf c ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hc2
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
      · exact absurd (orderOf_eq_one_iff.mp h1) hcne
      · exact h2
    have hcV : ((c : ↥C) : G) ∈ V :=
      hinv (c : G) c.2 (by rw [Subgroup.orderOf_coe]; exact hord)
    have hcZ : c ∈ Subgroup.center ↥C := (hZV c).mpr hcV
    have : φ c ∈ Work.Higman.TwoStep.kerFst := by
      rw [← hcenter_eq, ← Subgroup.map_center_eq φ]
      exact (Subgroup.mem_map_iff_mem (f := (φ : ↥C →* Work.Higman.TwoStep A Z b))
        φ.injective).mpr hcZ
    have hfst : (φ c).fst = 0 := this
    have : u = 0 := by simpa [c, x] using hfst
    exact this

/-- The group of second coordinates of `kerFst` is `Z`. -/
private lemma card_kerFstB {A Z : Type*} [AddCommGroup A] [AddCommGroup Z] {b : A → A → Z}
    [Work.Higman.Biadd b] [Work.Higman.AddExpTwo A] [Work.Higman.AddExpTwo Z] :
    Nat.card ↥(Work.Higman.TwoStep.kerFst (A := A) (Z := Z) (b := b)) = Nat.card Z :=
  Nat.card_congr
    { toFun := fun x => (x : Work.Higman.TwoStep A Z b).snd
      invFun := fun z => ⟨⟨0, z⟩, rfl⟩
      left_inv := by
        intro x
        apply Subtype.ext
        exact Work.Higman.TwoStep.ext_iff (Work.Higman.TwoStep.mem_kerFst.mp x.2).symm rfl
      right_inv := by intro z; rfl }

/-- The centre of a two-step model is `kerFst`, as soon as the centre of the group it models
has order `8 = |Z|`. -/
private lemma twoStep_center_eq_kerFst {A Z : Type*} [AddCommGroup A] [AddCommGroup Z]
    [Work.Higman.AddExpTwo A] [Work.Higman.AddExpTwo Z] [Finite A] [Finite Z] {b : A → A → Z}
    [Work.Higman.Biadd b] {P : Type*} [Group P] (φ : P ≃* Work.Higman.TwoStep A Z b)
    (hZc : Nat.card ↥(Subgroup.center P) = 8) (hZcard : Nat.card Z = 8) :
    Subgroup.center (Work.Higman.TwoStep A Z b) = Work.Higman.TwoStep.kerFst := by
  have hker : Nat.card ↥(Work.Higman.TwoStep.kerFst (A := A) (Z := Z) (b := b)) = 8 := by
    rw [card_kerFstB, hZcard]
  have hcen : Nat.card ↥(Subgroup.center (Work.Higman.TwoStep A Z b)) = 8 := by
    have h1 : Nat.card ↥(Subgroup.center (Work.Higman.TwoStep A Z b)) =
        Nat.card ↥(Subgroup.center P) := by
      rw [← Subgroup.map_center_eq φ]
      exact Nat.card_congr ((Subgroup.equivMapOfInjective (Subgroup.center P)
        (φ : P →* Work.Higman.TwoStep A Z b) φ.injective).symm.toEquiv)
    rw [h1, hZc]
  exact (Subgroup.eq_of_le_of_card_ge (H := Work.Higman.TwoStep.kerFst)
    (K := Subgroup.center (Work.Higman.TwoStep A Z b))
    Work.Higman.TwoStep.kerFst_le_center (by rw [hker, hcen])).symm

/-- The `A`-coordinate projection of the two-step model, as a homomorphism onto the additive
group `A` (written multiplicatively). -/
private def fstHomB {A Z : Type*} [AddCommGroup A] [AddCommGroup Z] {b : A → A → Z}
    [Work.Higman.Biadd b] [Work.Higman.AddExpTwo A] [Work.Higman.AddExpTwo Z] :
    Work.Higman.TwoStep A Z b →* Multiplicative A where
  toFun x := Multiplicative.ofAdd x.fst
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The image of a subgroup of the type-`B` model in the `A`-coordinate, as an `𝔽₂`-subspace. -/
private def imgSubB {θ : F8 ≃+* F8} (ε : F8)
    (E : Subgroup (Work.Higman.TwoStep (F8 × F8) F8 (Work.Higman.bCocycle F8 θ ε))) :
    Submodule (ZMod 2) (F8 × F8) where
  carrier := {u | ∃ x ∈ E, x.fst = u}
  zero_mem' := ⟨1, E.one_mem, rfl⟩
  add_mem' := by
    rintro a c ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, E.mul_mem hx hy, rfl⟩
  smul_mem' := by
    intro r u hu
    rcases zmod_two_eq_zero_or_one r with rfl | rfl
    · refine ⟨1, E.one_mem, ?_⟩
      simp
    · simpa using hu

/-- Higman's `B(3,θ,ε)` with `θ ≠ 1` and an anisotropic `ε` has no abelian subgroup of order
`64`: a subgroup `E` containing `kerFst` with `|E| = 64` has image `W` of order `8` in
`A = GF(2³) × GF(2³)`, and if `E` were abelian the cocycle would be symmetric on the
`3`-dimensional subspace `W`, contradicting `noIsotropic_B3`. -/
private lemma bType_nonabelian {θ : F8 ≃+* F8} {ε : F8}
    (hθ : θ ≠ RingEquiv.refl _)
    (haniso : ∀ a c : F8, a * θ a + ε * (a * θ c) + c * θ c = 0 → a = 0 ∧ c = 0)
    (E : Subgroup (Work.Higman.TwoStep (F8 × F8) F8 (Work.Higman.bCocycle F8 θ ε)))
    (hker : Work.Higman.TwoStep.kerFst ≤ E) (hcard : Nat.card ↥E = 64) :
    ∃ x y : ↥E, x * y ≠ y * x := by
  classical
  by_contra hcon
  push_neg at hcon
  have hcardF8 : Nat.card F8 = 8 := f8_card
  have hkerFst_card : Nat.card ↥(Work.Higman.TwoStep.kerFst (A := F8 × F8) (Z := F8)
      (b := Work.Higman.bCocycle F8 θ ε)) = 8 := by
    rw [card_kerFstB, hcardF8]
  set f : ↥E →* Multiplicative (F8 × F8) :=
    (fstHomB (b := Work.Higman.bCocycle F8 θ ε)).comp E.subtype with hfdef
  have hfker : ∀ x : ↥E,
      x ∈ f.ker ↔ ((x : Work.Higman.TwoStep (F8 × F8) F8 (Work.Higman.bCocycle F8 θ ε)) ∈
        Work.Higman.TwoStep.kerFst) := by
    intro x
    constructor
    · intro h
      rw [Work.Higman.TwoStep.mem_kerFst]
      have h1 : Multiplicative.toAdd (f x) = 0 := by rw [h]; rfl
      simpa [f, fstHomB, MonoidHom.comp_apply] using h1
    · intro h
      have h1 : ((x : Work.Higman.TwoStep (F8 × F8) F8
          (Work.Higman.bCocycle F8 θ ε)).fst) = 0 := Work.Higman.TwoStep.mem_kerFst.mp h
      show f x = 1
      simp [f, fstHomB, MonoidHom.comp_apply, h1]
  have hker_card : Nat.card ↥f.ker = 8 := by
    have hbij : Nat.card ↥f.ker = Nat.card ↥(Work.Higman.TwoStep.kerFst (A := F8 × F8)
        (Z := F8) (b := Work.Higman.bCocycle F8 θ ε)) :=
      Nat.card_congr
        { toFun := fun x => ⟨(x.1 : Work.Higman.TwoStep (F8 × F8) F8
              (Work.Higman.bCocycle F8 θ ε)), (hfker x.1).mp x.2⟩
          invFun := fun y => ⟨⟨y.1, hker y.2⟩, (hfker ⟨y.1, hker y.2⟩).mpr y.2⟩
          left_inv := fun x => Subtype.ext rfl
          right_inv := fun y => Subtype.ext rfl }
    rw [hbij, hkerFst_card]
  set W : Submodule (ZMod 2) (F8 × F8) := imgSubB ε E with hWdef
  have hWcard_eq : Nat.card ↥W = Nat.card ↥f.range :=
    Nat.card_congr
      { toFun := fun u => ⟨Multiplicative.ofAdd u.1, by
          obtain ⟨x, hx, hxu⟩ := u.2
          refine ⟨⟨x, hx⟩, ?_⟩
          show Multiplicative.ofAdd x.fst = Multiplicative.ofAdd u.1
          rw [hxu]⟩
        invFun := fun y => ⟨Multiplicative.toAdd y.1, by
          obtain ⟨x, hx⟩ := y.2
          refine ⟨x.1, x.2, ?_⟩
          have h : f x = Multiplicative.ofAdd
              (x.1 : Work.Higman.TwoStep (F8 × F8) F8 (Work.Higman.bCocycle F8 θ ε)).fst := rfl
          rw [h] at hx
          exact congrArg Multiplicative.toAdd hx⟩
        left_inv := fun u => Subtype.ext rfl
        right_inv := fun y => Subtype.ext rfl }
  have hWcard : Nat.card ↥W = 8 := by
    rw [hWcard_eq]
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [hcard, hker_card] at h1
    have h3 : Nat.card (↥E ⧸ f.ker) = 8 := by omega
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    exact h3
  have hfinrank : Module.finrank (ZMod 2) W = 3 := by
    haveI : Module.Finite (ZMod 2) W := Module.Finite.of_finite
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
    rw [hWcard, Nat.card_zmod] at h
    have h2 : (2 : ℕ) ^ Module.finrank (ZMod 2) W = 2 ^ 3 := by rw [← h]; norm_num
    exact Nat.pow_right_injective (by norm_num) h2
  have hsym : ∀ u v : ↥W, Work.Higman.bCocycle F8 θ ε u.1 v.1 =
      Work.Higman.bCocycle F8 θ ε v.1 u.1 := by
    intro u v
    obtain ⟨x, hx, hxu⟩ := u.2
    obtain ⟨y, hy, hyv⟩ := v.2
    have hcomm : x * y = y * x := congrArg Subtype.val (hcon ⟨x, hx⟩ ⟨y, hy⟩)
    have h2 := congrArg (fun t : Work.Higman.TwoStep (F8 × F8) F8
      (Work.Higman.bCocycle F8 θ ε) => t.snd) hcomm
    rw [Work.Higman.TwoStep.snd_mul, Work.Higman.TwoStep.snd_mul, hxu, hyv] at h2
    have h6 : x.snd + (y.snd + Work.Higman.bCocycle F8 θ ε u.1 v.1) =
        x.snd + (y.snd + Work.Higman.bCocycle F8 θ ε v.1 u.1) := by
      rw [← add_assoc, ← add_assoc, h2]
      abel
    exact add_left_cancel (add_left_cancel h6)
  exact (Work.Hering.HardCore.noIsotropic_B3 θ ε hθ haniso) ⟨W, hfinrank, hsym⟩

theorem nonAbelianCase {G : Type} [Group G] [Finite G]
    (hHig : Work.Higman.HigmanClassProp) (hVIII1 : AppVIIIProp1) (hVIII3 : AppVIIIProp3)
    (hVIII4 : AppVIIIProp4) (hIX : AppIXProp) : NonAbelianCaseProp (G := G) := by
  intro V C hV hcard hexp hC hC2 hinv hAut hnotab
  obtain ⟨hSuz, hZcard, hCns⟩ := reduction V C hV hcard hexp hC hC2 hinv hAut hnotab hHig
  obtain ⟨-, -, -, hcardor, -⟩ := hHig.1 ↥C hSuz
  rcases hcardor with hq2 | hq3
  · exact hCns (q2_aut_solvable hHig.1 hVIII1 hSuz hq2)
  · -- the order-`q³` case (Peterfalvi I §4, second half)
    obtain ⟨hcenterC, -, -, -, -⟩ := hHig.1 ↥C hSuz
    have hZV : ∀ z : ↥C, z ∈ Subgroup.center ↥C ↔ ((z : G) ∈ V) := by
      intro z
      rw [hcenterC]
      constructor
      · intro hz
        have hz2 : (z : G) ^ 2 = 1 := by
          have h := congrArg (fun t : ↥C => (t : G)) hz
          simpa using h
        rcases eq_or_ne (z : G) 1 with h1 | h1
        · rw [h1]; exact V.one_mem
        · exact hinv (z : G) z.2 (orderOf_eq_prime hz2 h1)
      · intro hz
        show z ^ 2 = 1
        exact Subtype.ext (by simpa [pow_two] using hexp (z : G) hz)
    obtain ⟨n, e, θ, ε, hZn, hodd, hcase⟩ := hHig.2 ↥C hSuz hq3
    have hn : n = 3 := by
      have h2n : (2 : ℕ) ^ n = 8 := hZn.symm.trans hZcard
      have hpow : (2 : ℕ) ^ n = 2 ^ 3 := by rw [h2n]; norm_num
      exact (Nat.pow_right_injective (by norm_num : 2 ≤ 2)) hpow
    subst hn
    rcases hcase with ⟨hε0, hεad, hlawB⟩ | ⟨hθ2, hεad, hlawC⟩ | ⟨hθ5, hθrefl, h5n, hεad, hlawD⟩
    · -- type `B(3,θ,ε)`
      let b : (GaloisField 2 3 × GaloisField 2 3) → (GaloisField 2 3 × GaloisField 2 3) →
          GaloisField 2 3 := Work.Higman.bCocycle (GaloisField 2 3) θ ε
      haveI : Work.Higman.Biadd b := inferInstance
      haveI : Work.Higman.AddExpTwo (GaloisField 2 3 × GaloisField 2 3) := inferInstance
      haveI : Work.Higman.AddExpTwo (GaloisField 2 3) := inferInstance
      haveI : Finite (GaloisField 2 3) := inferInstance
      have hiso : ↥C ≃* Work.Higman.TwoStep (GaloisField 2 3 × GaloisField 2 3)
          (GaloisField 2 3) b := twoStepIso b e (by simpa only [b] using hlawB)
      have hns : ¬ Group.IsSolvable (MulAut (Work.Higman.TwoStep
          (GaloisField 2 3 × GaloisField 2 3) (GaloisField 2 3) b)) := by
        intro hsol
        haveI : Group.IsSolvable (MulAut (Work.Higman.TwoStep
            (GaloisField 2 3 × GaloisField 2 3) (GaloisField 2 3) b)) := hsol
        exact hCns (Group.isSolvable_of_surjective (f := (MulAut.congr hiso).symm.toMonoidHom)
          (MulAut.congr hiso).symm.surjective)
      have hZc : Nat.card ↥(Subgroup.center ↥C) = 8 := hZcard
      have hcardZ : Nat.card (GaloisField 2 3) = 8 := by
        rw [GaloisField.card 2 3 (by norm_num)]; norm_num
      have haniso := bAniso V C hexp b hiso hZV hZc hcardZ hinv
      by_cases hθ : θ = RingEquiv.refl (GaloisField 2 3)
      · -- `θ = 1`: App. VIII Prop. 3
        subst hθ
        have haniso' : ∀ a b' : GaloisField 2 3,
            a * a + ε * (a * b') + b' * b' = 0 → a = 0 ∧ b' = 0 := by
          intro a b' h
          have h2 : b (a, b') (a, b') = 0 := by
            simpa only [b, Work.Higman.bCocycle, RingEquiv.refl_apply] using h
          have := haniso (a, b') h2
          simpa using this
        have hs := hVIII3 3 ε haniso'
        exact hns (by simpa only [b, Work.Higman.BType] using hs)
      · -- `θ ≠ 1`: Higman's `B(3,θ,ε)` with `θ ≠ 1` has no abelian subgroup of order `64`
        -- (`noIsotropic_B3`); so a normal subgroup `D` of order `64` between `V` and `C`
        -- (Higman's module argument, App. IX) is a non-abelian Suzuki 2-group with
        -- `|Z(D)| = 8`; Higman's classification of the `q²` case makes `Aut(D)` solvable,
        -- contradicting `D ⊴ G` and `G/C ≅ GL(3,2) ∩ Aut(D)`.
        have haniso'' : ∀ a c : GaloisField 2 3,
            a * θ a + ε * (a * θ c) + c * θ c = 0 → a = 0 ∧ c = 0 := by
          intro a c h
          have h2 : b (a, c) (a, c) = 0 := by
            simpa only [b, Work.Higman.bCocycle] using h
          have h3 := haniso (a, c) h2
          exact ⟨congrArg Prod.fst h3, congrArg Prod.snd h3⟩
        obtain ⟨D, hDn, hDleC, hVD, hDcard⟩ :=
          Work.Hering.HardCore.q3_module hHig hIX V C hV hcard hexp hC hC2 hinv hAut
            hnotab hSuz hZcard hq3
        have hnonab : ¬ ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := by
          intro hab
          let Dsub : Subgroup ↥C := D.subgroupOf C
          have hcardDsub : Nat.card ↥Dsub = 64 := by
            rw [show Nat.card ↥Dsub = Nat.card ↥D from
              Nat.card_congr
                { toFun := fun x => ⟨((x : ↥C) : G), Subgroup.mem_subgroupOf.mp x.2⟩
                  invFun := fun y => ⟨⟨(y : G), hDleC y.2⟩, Subgroup.mem_subgroupOf.mpr y.2⟩
                  left_inv := fun x => Subtype.ext rfl
                  right_inv := fun y => Subtype.ext rfl }, hDcard]
          let E : Subgroup (Work.Higman.TwoStep (GaloisField 2 3 × GaloisField 2 3)
              (GaloisField 2 3) b) :=
            Dsub.map (hiso : ↥C →* Work.Higman.TwoStep (GaloisField 2 3 × GaloisField 2 3)
              (GaloisField 2 3) b)
          have hcardE : Nat.card ↥E = 64 := by
            rw [show Nat.card ↥E = Nat.card ↥Dsub from
              Subgroup.card_map_of_injective hiso.injective, hcardDsub]
          have hkerE : Work.Higman.TwoStep.kerFst ≤ E := by
            have hcent : Subgroup.center (Work.Higman.TwoStep (GaloisField 2 3 × GaloisField 2 3)
                (GaloisField 2 3) b) = Work.Higman.TwoStep.kerFst :=
              twoStep_center_eq_kerFst hiso hZc hcardZ
            rw [← hcent, ← Subgroup.map_center_eq hiso]
            exact Subgroup.map_mono fun z hz =>
              Subgroup.mem_subgroupOf.mpr (hVD ((hZV z).mp hz))
          have hEab : ∀ x y : ↥E, x * y = y * x := by
            intro x y
            obtain ⟨x', hx', hxeq⟩ := Subgroup.mem_map.mp x.2
            obtain ⟨y', hy', hyeq⟩ := Subgroup.mem_map.mp y.2
            apply Subtype.ext
            show x.1 * y.1 = y.1 * x.1
            rw [← hxeq, ← hyeq, ← map_mul, ← map_mul]
            congr 1
            apply Subtype.ext
            exact hab (x' : G) (Subgroup.mem_subgroupOf.mp hx') (y' : G)
              (Subgroup.mem_subgroupOf.mp hy')
          obtain ⟨u, v, huv⟩ := bType_nonabelian hθ haniso'' E hkerE hcardE
          exact huv (hEab u v)
        obtain ⟨hSuzD, -⟩ := Work.Hering.HardCore.q3_suzuki_sixtyfour hHig V C D hV hcard
          hexp hC hC2 hinv hAut hnotab hVD hDleC hDn hDcard hnonab
        exact Work.Hering.HardCore.q3_nonabelian_false hHig V C D hV hcard hexp hC hC2 hinv
          hAut hnotab hVD hDleC hDn hDcard hnonab hSuzD
    · -- type `C(3,ε)`: `θ` is the Frobenius of `GF(2³)`, so `C` is canonically the model
      -- `AppVIII.CTypeC 1 ε`; App. VIII Prop. 4 (the stabiliser of `P₁` in `Aut(C(n,ε))` is
      -- solvable) together with `cTypeP1_top` (every automorphism stabilises `P₁`) then
      -- contradicts `hCns`.
      have hθ : θ = Work.Hering.AppVIII.thetaC 1 :=
        Work.Hering.HardCore.cTheta_eq_thetaC θ hθ2
      rw [hθ] at hlawC
      let b' : (GaloisField 2 3 × GaloisField 2 3) → (GaloisField 2 3 × GaloisField 2 3) →
          GaloisField 2 3 :=
        Work.Higman.cCocycle (GaloisField 2 3) (Work.Hering.AppVIII.thetaC 1) ε
      haveI : Work.Higman.Biadd b' := inferInstance
      haveI : Work.Higman.AddExpTwo (GaloisField 2 3 × GaloisField 2 3) := inferInstance
      haveI : Work.Higman.AddExpTwo (GaloisField 2 3) := inferInstance
      haveI : Finite (GaloisField 2 3) := inferInstance
      have hiso : ↥C ≃* Work.Hering.AppVIII.CTypeC 1 ε :=
        twoStepIso b' e (by simpa only [b'] using hlawC)
      have hns : ¬ Group.IsSolvable (MulAut (Work.Hering.AppVIII.CTypeC 1 ε)) := by
        intro hsol
        haveI := hsol
        exact hCns (Group.isSolvable_of_surjective (f := (MulAut.congr hiso).symm.toMonoidHom)
          (MulAut.congr hiso).symm.surjective)
      have hcardZ : Nat.card (GaloisField 2 3) = 8 := by
        rw [GaloisField.card 2 3 (by norm_num)]; norm_num
      have haniso := bAniso V C hexp b' hiso hZV hZcard hcardZ hinv
      have haniso4 : ∀ x y : GaloisField 2 3,
          x * (Work.Hering.AppVIII.thetaC 1 x) +
            ε * (Work.Higman.sqrtF (GaloisField 2 3) x *
              Work.Hering.AppVIII.thetaC 1 (y * y)) + y * y = 0 → x = 0 ∧ y = 0 := by
        intro x y h
        have h2 : b' (x, y) (x, y) = 0 := by
          simpa only [b', Work.Higman.cCocycle] using h
        have h3 := haniso (x, y) h2
        exact ⟨congrArg Prod.fst h3, congrArg Prod.snd h3⟩
      have hsol : Group.IsSolvable (MulAut (Work.Hering.AppVIII.CTypeC 1 ε)) := by
        have h4 := hVIII4 1 ε (le_refl 1) haniso4
        haveI : Group.IsSolvable
            ↥(Work.Hering.stabilizerMulAut (Work.Hering.AppVIII.P1C 1 ε)) := h4
        have hsurj : Function.Surjective
            (Work.Hering.stabilizerMulAut (Work.Hering.AppVIII.P1C 1 ε)).subtype :=
          fun α => ⟨⟨α, Work.Hering.AppVIII.cTypeP1_top ε haniso4 α⟩, rfl⟩
        exact Group.isSolvable_of_surjective hsurj
      exact hns hsol
    · -- type `D(3,θ,ε)`: excluded, since `5 ∤ 3`
      obtain ⟨k, hk⟩ := h5n
      omega

end Work.Hering.HardCore
