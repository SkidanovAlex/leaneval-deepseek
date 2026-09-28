import Mathlib
import Submission.Work.Cohomology.SmallChains
import Submission.Work.Cohomology.SmallChainsIsoAux
import Submission.Work.Cohomology.smallProj_spec

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory
open AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

namespace Ct

noncomputable section

variable {X : TopCat}

/-! ## The projection onto the small chains and its complement -/

/-- `θ n = r n ≫ smallToSing.f n`, the projection of the singular chains onto the small chains. -/
def theta (U V : Set X) (r : ∀ n, (singularChains ℤ X).X n ⟶ (smallChains U V).X n) (n : ℕ) :
    (singularChains ℤ X).X n ⟶ (singularChains ℤ X).X n :=
  r n ≫ (smallToSing U V).f n

/-- `π n = 𝟙 - θ n`, the projection onto the complement of the small chains. -/
def pi (U V : Set X) (r : ∀ n, (singularChains ℤ X).X n ⟶ (smallChains U V).X n) (n : ℕ) :
    (singularChains ℤ X).X n ⟶ (singularChains ℤ X).X n :=
  𝟙 ((singularChains ℤ X).X n) - theta U V r n

/-- The `n`-th term of the contraction equation: `E n = κ n ≫ ∂ + ∂ ≫ κ (n-1) - 𝟙`
(as a function, `x ↦ ∂(κ n x) + κ (n-1) (∂ x) - x`). -/
def Eterm (n : ℕ) (km : (singularChains ℤ X).X n ⟶ (singularChains ℤ X).X (n + 1))
    (km1 : (singularChains ℤ X).X (n - 1) ⟶ (singularChains ℤ X).X n) :
    (singularChains ℤ X).X n ⟶ (singularChains ℤ X).X n :=
  km ≫ (singularChains ℤ X).d (n + 1) n
    + (singularChains ℤ X).d n (n - 1) ≫ km1
    - 𝟙 ((singularChains ℤ X).X n)

/-- In degree `0` the `κ (-1)` term of `E` is absent (`∂ 0 (-1) = 0`). -/
theorem Eterm_zero (km : (singularChains ℤ X).X 0 ⟶ (singularChains ℤ X).X 1)
    (km1 : (singularChains ℤ X).X (0 - 1) ⟶ (singularChains ℤ X).X 0) :
    Eterm 0 km km1 = km ≫ (singularChains ℤ X).d 1 0 - 𝟙 ((singularChains ℤ X).X 0) := by
  have hd : (singularChains ℤ X).d 0 (0 - 1) = 0 :=
    HomologicalComplex.shape _ 0 (0 - 1) (by rw [ComplexShape.down_Rel]; omega)
  dsimp only [Eterm]
  rw [hd, zero_comp, add_zero]

/-- In positive degrees, `E (m+1)` written with the two explicit components. -/
theorem Eterm_succ (m : ℕ) (km : (singularChains ℤ X).X (m + 1) ⟶ (singularChains ℤ X).X (m + 2))
    (km1 : (singularChains ℤ X).X m ⟶ (singularChains ℤ X).X (m + 1)) :
    Eterm (m + 1) km km1 = km ≫ (singularChains ℤ X).d (m + 2) (m + 1)
      + (singularChains ℤ X).d (m + 1) m ≫ km1
      - 𝟙 ((singularChains ℤ X).X (m + 1)) := by
  dsimp only [Eterm]
  rfl

/-! ## Elementary properties of `θ` and `π` -/

theorem theta_idem (U V : Set X) (r : ∀ n, (singularChains ℤ X).X n ⟶ (smallChains U V).X n)
    (hr1 : ∀ n, (smallToSing U V).f n ≫ r n = 𝟙 ((smallChains U V).X n)) (n : ℕ) :
    theta U V r n ≫ theta U V r n = theta U V r n := by
  show (r n ≫ (smallToSing U V).f n) ≫ (r n ≫ (smallToSing U V).f n)
    = r n ≫ (smallToSing U V).f n
  simp only [Category.assoc]
  rw [← Category.assoc ((smallToSing U V).f n) (r n) ((smallToSing U V).f n), hr1 n,
    Category.id_comp]

theorem pi_eq (U V : Set X) (r : ∀ n, (singularChains ℤ X).X n ⟶ (smallChains U V).X n) (n : ℕ) :
    pi U V r n = 𝟙 ((singularChains ℤ X).X n) - theta U V r n := rfl

theorem pi_theta (U V : Set X) (r : ∀ n, (singularChains ℤ X).X n ⟶ (smallChains U V).X n)
    (hr1 : ∀ n, (smallToSing U V).f n ≫ r n = 𝟙 ((smallChains U V).X n)) (n : ℕ) :
    pi U V r n ≫ theta U V r n = 0 := by
  rw [pi, CategoryTheory.Preadditive.sub_comp, Category.id_comp, theta_idem U V r hr1, sub_self]

theorem theta_pi (U V : Set X) (r : ∀ n, (singularChains ℤ X).X n ⟶ (smallChains U V).X n)
    (hr1 : ∀ n, (smallToSing U V).f n ≫ r n = 𝟙 ((smallChains U V).X n)) (n : ℕ) :
    theta U V r n ≫ pi U V r n = 0 := by
  rw [pi, CategoryTheory.Preadditive.comp_sub, Category.comp_id, theta_idem U V r hr1, sub_self]

theorem theta_add_pi (U V : Set X) (r : ∀ n, (singularChains ℤ X).X n ⟶ (smallChains U V).X n)
    (n : ℕ) : theta U V r n + pi U V r n = 𝟙 ((singularChains ℤ X).X n) := by
  rw [pi]; abel

theorem pi_idem (U V : Set X) (r : ∀ n, (singularChains ℤ X).X n ⟶ (smallChains U V).X n)
    (hr1 : ∀ n, (smallToSing U V).f n ≫ r n = 𝟙 ((smallChains U V).X n)) (n : ℕ) :
    pi U V r n ≫ pi U V r n = pi U V r n := by
  calc pi U V r n ≫ pi U V r n
      = 𝟙 ((singularChains ℤ X).X n) ≫ pi U V r n - theta U V r n ≫ pi U V r n := by
        rw [pi, CategoryTheory.Preadditive.sub_comp]
    _ = pi U V r n - 0 := by rw [Category.id_comp, theta_pi U V r hr1]
    _ = pi U V r n := sub_zero _

/-- `θ n x` is a small chain. -/
theorem theta_mem (U V : Set X) (r : ∀ n, (singularChains ℤ X).X n ⟶ (smallChains U V).X n)
    (n : ℕ) (x : (singularChains ℤ X).X n) :
    IsSmallChain U V ((theta U V r n).hom x) := by
  show ((smallToSing U V).f n).hom ((r n).hom x) ∈ smallChainSubmodule U V n
  exact ⟨(r n).hom x, rfl⟩

/-- A small chain is fixed by `θ`. -/
theorem theta_eq_of_small (U V : Set X)
    (r : ∀ n, (singularChains ℤ X).X n ⟶ (smallChains U V).X n)
    (hr1 : ∀ n, (smallToSing U V).f n ≫ r n = 𝟙 ((smallChains U V).X n))
    (n : ℕ) {x : (singularChains ℤ X).X n} (hx : IsSmallChain U V x) :
    (theta U V r n).hom x = x := by
  obtain ⟨a, ha⟩ := hx
  show ((smallToSing U V).f n).hom ((r n).hom x) = x
  rw [← ha]
  have h : (r n).hom (((smallToSing U V).f n).hom a) = a := by
    have h2 := congrArg (fun (g : (smallChains U V).X n ⟶ (smallChains U V).X n) => g.hom a)
      (hr1 n)
    simpa [ModuleCat.hom_comp, LinearMap.comp_apply] using h2
  rw [h]

theorem small_iff_theta (U V : Set X)
    (r : ∀ n, (singularChains ℤ X).X n ⟶ (smallChains U V).X n)
    (hr1 : ∀ n, (smallToSing U V).f n ≫ r n = 𝟙 ((smallChains U V).X n))
    (n : ℕ) (x : (singularChains ℤ X).X n) :
    IsSmallChain U V x ↔ (theta U V r n).hom x = x :=
  ⟨fun hx => theta_eq_of_small U V r hr1 n hx, fun h => by
    rw [← h]
    exact ⟨(r n).hom x, rfl⟩⟩

theorem small_iff_pi (U V : Set X)
    (r : ∀ n, (singularChains ℤ X).X n ⟶ (smallChains U V).X n)
    (hr1 : ∀ n, (smallToSing U V).f n ≫ r n = 𝟙 ((smallChains U V).X n))
    (n : ℕ) (x : (singularChains ℤ X).X n) :
    IsSmallChain U V x ↔ (pi U V r n).hom x = 0 := by
  have hval : (pi U V r n).hom x = x - (theta U V r n).hom x := by
    rw [pi]; simp
  rw [hval]
  constructor
  · intro h; rw [((small_iff_theta U V r hr1 n x).mp h), sub_self]
  · intro h; exact (small_iff_theta U V r hr1 n x).mpr (sub_eq_zero.mp h).symm

theorem pi_kills_small (U V : Set X)
    (r : ∀ n, (singularChains ℤ X).X n ⟶ (smallChains U V).X n)
    (hr1 : ∀ n, (smallToSing U V).f n ≫ r n = 𝟙 ((smallChains U V).X n))
    (n : ℕ) {x : (singularChains ℤ X).X n} (hx : IsSmallChain U V x) :
    (pi U V r n).hom x = 0 :=
  (small_iff_pi U V r hr1 n x).mp hx

theorem pi_theta_apply (U V : Set X)
    (r : ∀ n, (singularChains ℤ X).X n ⟶ (smallChains U V).X n)
    (hr1 : ∀ n, (smallToSing U V).f n ≫ r n = 𝟙 ((smallChains U V).X n))
    (n : ℕ) (x : (singularChains ℤ X).X n) :
    (theta U V r n).hom ((pi U V r n).hom x) = 0 := by
  have h := congrArg (fun (g : (singularChains ℤ X).X n ⟶ (singularChains ℤ X).X n) =>
    g.hom x) (pi_theta U V r hr1 n)
  simpa [ModuleCat.hom_comp, LinearMap.comp_apply] using h

theorem theta_pi_apply (U V : Set X)
    (r : ∀ n, (singularChains ℤ X).X n ⟶ (smallChains U V).X n)
    (hr1 : ∀ n, (smallToSing U V).f n ≫ r n = 𝟙 ((smallChains U V).X n))
    (n : ℕ) (x : (singularChains ℤ X).X n) :
    (pi U V r n).hom ((theta U V r n).hom x) = 0 := by
  have h := congrArg (fun (g : (singularChains ℤ X).X n ⟶ (singularChains ℤ X).X n) =>
    g.hom x) (theta_pi U V r hr1 n)
  simpa [ModuleCat.hom_comp, LinearMap.comp_apply] using h

theorem pi_apply_eq (U V : Set X) (r : ∀ n, (singularChains ℤ X).X n ⟶ (smallChains U V).X n)
    (n : ℕ) (x : (singularChains ℤ X).X n) :
    (pi U V r n).hom x = x - (theta U V r n).hom x := by
  rw [pi]; simp

/-! ## The boundary of a small chain is small -/

theorem isSmallChain_d {U V : Set X} {n : ℕ} {c : (singularChains ℤ X).X n}
    (hc : IsSmallChain U V c) :
    IsSmallChain U V (((singularChains ℤ X).d n (n-1)).hom c) := by
  obtain ⟨a, ha⟩ := hc
  refine ⟨((smallChains U V).d n (n-1)).hom a, ?_⟩
  rw [← ha]
  have h := HomologicalComplex.Hom.comm (smallToSing U V) n (n-1)
  have h2 := congrArg (fun (g : (smallChains U V).X n ⟶ (singularChains ℤ X).X (n-1)) =>
    g.hom a) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  exact h2.symm

/-- A morphism out of the singular `n`-chains is determined by its values on the generators. -/
theorem eq_of_gen {n : ℕ} {M : ModuleCat ℤ} {f g : (singularChains ℤ X).X n ⟶ M}
    (h : ∀ σ : Simplex X n, f.hom (gen X n σ) = g.hom (gen X n σ)) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  have htop : LinearMap.ker (f.hom - g.hom) = ⊤ := by
    apply mem_of_gen X n
    intro σ
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    exact h σ
  have := Submodule.eq_top_iff'.mp htop c
  simpa [LinearMap.mem_ker, sub_eq_zero] using this

/-- A morphism out of the singular `n`-chains which kills the generators is zero. -/
theorem eq_zero_of_gen {n : ℕ} {M : ModuleCat ℤ} {f : (singularChains ℤ X).X n ⟶ M}
    (h : ∀ σ : Simplex X n, f.hom (gen X n σ) = 0) : f = 0 :=
  eq_of_gen fun σ => by rw [h σ]; rfl

/-- A morphism `X n ⟶ M` is zero iff it vanishes on every element. -/
theorem eq_zero_iff {n : ℕ} {M : ModuleCat ℤ} (f : (singularChains ℤ X).X n ⟶ M) :
    f = 0 ↔ ∀ x, f.hom x = 0 := by
  constructor
  · intro h x; rw [h]; rfl
  · intro h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simpa using h x

/-- The generators of the chain complex of an arbitrary simplicial set span it. -/
theorem mem_of_gen_SSet (Y : SSet) (n : ℕ)
    (P : Submodule ℤ ↥((Y.chainComplex (ModuleCat.of ℤ ℤ)).X n))
    (hgen : ∀ y : Y _⦋n⦌, genSSet Y n y ∈ P) : P = ⊤ := by
  letI : Module ℤ (↥((Y.chainComplex (ModuleCat.of ℤ ℤ)).X n) ⧸ P) := Submodule.Quotient.module P
  let q : (Y.chainComplex (ModuleCat.of ℤ ℤ)).X n ⟶
      ModuleCat.of ℤ (↥((Y.chainComplex (ModuleCat.of ℤ ℤ)).X n) ⧸ P) :=
    ModuleCat.ofHom (Submodule.mkQ P)
  have hleg : ∀ y : Y _⦋n⦌, Y.ιChainComplex (R := ModuleCat.of ℤ ℤ) y ≫ q = 0 := by
    intro y
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply]
    change Submodule.Quotient.mk (genSSet Y n y) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact hgen y
  have hq : q = 0 := by
    apply SSet.chainComplex_hom_ext (X := Y) (R := ModuleCat.of ℤ ℤ) (n := n)
    intro y
    simpa using hleg y
  refine Submodule.eq_top_iff'.mpr fun c => ?_
  have h2 : ModuleCat.Hom.hom q c = ModuleCat.Hom.hom (0 : (Y.chainComplex (ModuleCat.of ℤ ℤ)).X n ⟶
      ModuleCat.of ℤ (↥((Y.chainComplex (ModuleCat.of ℤ ℤ)).X n) ⧸ P)) c := by rw [hq]
  rw [ModuleCat.hom_zero, LinearMap.zero_apply] at h2
  have h3 : ModuleCat.Hom.hom q = Submodule.mkQ P := rfl
  rw [h3, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h2
  exact h2

/-- A linear map which kills the generators of all small simplices kills every small chain. -/
theorem kills_small_of_gen_kills {U V : Set X} {n : ℕ} {M : ModuleCat ℤ}
    (T : (singularChains ℤ X).X n ⟶ M)
    (h : ∀ (σ : Simplex X n) (hσ : IsSmall U V σ), T.hom (gen X n σ) = 0) :
    ∀ c, IsSmallChain U V c → T.hom c = 0 := by
  intro c hc
  obtain ⟨a, ha⟩ := hc
  rw [← ha]
  have hP : LinearMap.ker (ModuleCat.Hom.hom ((smallToSing U V).f n ≫ T)) = ⊤ := by
    apply mem_of_gen_SSet (Y := smallSSet U V) (n := n)
    intro σ'
    show (ModuleCat.Hom.hom ((smallToSing U V).f n ≫ T))
      (genSSet (smallSSet U V) n σ') = 0
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [smallToSing_gen σ']
    exact h σ'.1 σ'.2
  have := Submodule.eq_top_iff'.mp hP a
  simpa [LinearMap.mem_ker, ModuleCat.hom_comp, LinearMap.comp_apply] using this

/-- Prescribe a morphism out of the singular `n`-chains by its values on the generators. -/
def genDesc (n : ℕ) {M : ModuleCat ℤ} (v : Simplex X n → M) :
    (singularChains ℤ X).X n ⟶ M :=
  Cofan.IsColimit.desc ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
    (fun σ => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ (v σ)))

theorem genDesc_gen (n : ℕ) {M : ModuleCat ℤ} (v : Simplex X n → M) (σ : Simplex X n) :
    (genDesc (X := X) n v).hom (gen X n σ) = v σ := by
  have h := Cofan.IsColimit.fac
    ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
    (fun σ => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ (v σ))) σ
  have h2 := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶ M) => g.hom (1 : ℤ)) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply_one] at h2
  rw [genDesc, gen]
  exact h2

/-- A morphism into `X n` which is killed by `π n` on every generator is killed by `π n`
everywhere. -/
theorem pi_comp_of_gen {U V : Set X}
    (r : ∀ n, (singularChains ℤ X).X n ⟶ (smallChains U V).X n) (n : ℕ)
    (T : (singularChains ℤ X).X n ⟶ (singularChains ℤ X).X n)
    (h : ∀ σ : Simplex X n, (pi U V r n).hom (T.hom (gen X n σ)) = 0) :
    ∀ x, (pi U V r n).hom (T.hom x) = 0 := by
  have htop : LinearMap.ker (ModuleCat.Hom.hom (T ≫ pi U V r n)) = ⊤ := by
    apply mem_of_gen X n
    intro σ
    simp only [LinearMap.mem_ker, ModuleCat.hom_comp, LinearMap.comp_apply]
    exact h σ
  intro x
  have hx := Submodule.eq_top_iff'.mp htop x
  simpa [LinearMap.mem_ker, ModuleCat.hom_comp, LinearMap.comp_apply] using hx

/-! ## The state of the induction

The contraction is built degree by degree.  The state in degree `m` records the component
`κ m` together with the component `κ (m-1)` of the degree below (which is needed to write the
contraction equation in degree `m`), the two "projection" conditions and the contraction
equation in degree `m` (in the form `π m (E m x) = 0` for all `x`).
-/
structure CState (U V : Set X) (r : ∀ n, (singularChains ℤ X).X n ⟶ (smallChains U V).X n)
    (m : ℕ) where
  km : (singularChains ℤ X).X m ⟶ (singularChains ℤ X).X (m + 1)
  km1 : (singularChains ℤ X).X (m - 1) ⟶ (singularChains ℤ X).X m
  hkill : ∀ c : (singularChains ℤ X).X m, IsSmallChain U V c → km.hom c = 0
  hcompl : km ≫ (r (m + 1) ≫ (smallToSing U V).f (m + 1)) = 0
  hInv : ∀ x : (singularChains ℤ X).X m, (pi U V r m).hom ((Eterm m km km1).hom x) = 0

/-- The contraction equation in degree `m`, for cycles of degree `m`: the `κ (m-1)` term drops
out because it is applied to the boundary of a cycle. -/
theorem inv_cycles (U V : Set X) (r : ∀ n, (singularChains ℤ X).X n ⟶ (smallChains U V).X n)
    (m : ℕ) (km : (singularChains ℤ X).X m ⟶ (singularChains ℤ X).X (m + 1))
    (km1 : (singularChains ℤ X).X (m - 1) ⟶ (singularChains ℤ X).X m)
    (hInv : ∀ x : (singularChains ℤ X).X m, (pi U V r m).hom ((Eterm m km km1).hom x) = 0) :
    ∀ z : (singularChains ℤ X).X m, ((singularChains ℤ X).d m (m - 1)).hom z = 0 →
      (pi U V r m).hom (((singularChains ℤ X).d (m + 1) m).hom (km.hom z) - z) = 0 := by
  intro z hz
  have h := hInv z
  have hE : (Eterm m km km1).hom z
      = ((singularChains ℤ X).d (m + 1) m).hom (km.hom z) - z := by
    simp only [Eterm, ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_sub,
      LinearMap.sub_apply, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
      LinearMap.id_apply]
    rw [hz, map_zero, add_zero]
  rwa [hE] at h

/-- **The base of the induction**: the component `κ 0` of the contraction, together with its
properties.  Here `κ (-1)` does not occur (`∂ 0 (-1) = 0`). -/
theorem baseStateCore (U V : Set X) (r : ∀ n, (singularChains ℤ X).X n ⟶ (smallChains U V).X n)
    (hr1 : ∀ n, (smallToSing U V).f n ≫ r n = 𝟙 ((smallChains U V).X n))
    (hD : ∀ n (b : (singularChains ℤ X).X n),
      ((singularChains ℤ X).d n (n - 1)) b ∈ smallChainSubmodule U V (n - 1) →
      ∃ c : (singularChains ℤ X).X (n + 1),
        b - ((singularChains ℤ X).d (n + 1) n) c ∈ smallChainSubmodule U V n) :
    ∃ k0 : (singularChains ℤ X).X 0 ⟶ (singularChains ℤ X).X 1,
      (∀ c, IsSmallChain U V c → k0.hom c = 0) ∧
      (k0 ≫ (r 1 ≫ (smallToSing U V).f 1) = 0) ∧
      (∀ x : (singularChains ℤ X).X 0, (pi U V r 0).hom ((Eterm 0 k0 0).hom x) = 0) := by
  classical
  -- the hypothesis of `hD` in degree `0` is vacuous
  have hmem : ∀ σ : Simplex X 0,
      ((singularChains ℤ X).d 0 (0 - 1)).hom (gen X 0 σ)
        ∈ smallChainSubmodule U V (0 - 1) := by
    intro σ
    have hd : (singularChains ℤ X).d 0 (0 - 1) = 0 :=
      HomologicalComplex.shape _ 0 (0 - 1) (by rw [ComplexShape.down_Rel]; omega)
    rw [hd]
    exact (smallChainSubmodule U V (0 - 1)).zero_mem
  -- choose a filler for each `0`-simplex
  let c : Simplex X 0 → (singularChains ℤ X).X 1 :=
    fun σ => Classical.choose (hD 0 (gen X 0 σ) (hmem σ))
  have hc : ∀ σ : Simplex X 0,
      gen X 0 σ - ((singularChains ℤ X).d 1 0) (c σ) ∈ smallChainSubmodule U V 0 :=
    fun σ => Classical.choose_spec (hD 0 (gen X 0 σ) (hmem σ))
  -- prescribe `k0` on the generators: `0` on small simplices, `π 1 (c σ)` otherwise
  let k0 : (singularChains ℤ X).X 0 ⟶ (singularChains ℤ X).X 1 :=
    genDesc 0 (fun σ => if IsSmall U V σ then 0 else (pi U V r 1).hom (c σ))
  have hk0 : ∀ σ : Simplex X 0,
      k0.hom (gen X 0 σ) = if IsSmall U V σ then 0 else (pi U V r 1).hom (c σ) :=
    fun σ => genDesc_gen 0 _ σ
  refine ⟨k0, ?_, ?_, ?_⟩
  · exact kills_small_of_gen_kills k0 (fun σ hσ => by rw [hk0 σ]; simp [hσ])
  · apply eq_of_gen (M := (singularChains ℤ X).X 1)
    intro σ
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply]
    rw [hk0 σ]
    split_ifs with h
    · simp
    · exact pi_theta_apply U V r hr1 1 (c σ)
  · refine pi_comp_of_gen (U := U) (V := V) (r := r) 0 (Eterm 0 k0 0) ?_
    intro σ
    rw [Eterm_zero]
    simp only [ModuleCat.hom_sub, LinearMap.sub_apply, ModuleCat.hom_comp,
      LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply]
    rw [hk0 σ]
    split_ifs with h
    · rw [map_zero, zero_sub, map_neg,
        pi_kills_small U V r hr1 0 (isSmallChain_gen h), neg_zero]
    · -- `π 0 (∂ (π 1 (c σ))) = π 0 (∂ (c σ))` since `∂ (θ 1 (c σ))` is small
      have harg : ((singularChains ℤ X).d 1 0).hom ((pi U V r 1).hom (c σ)) - gen X 0 σ
          = (((singularChains ℤ X).d 1 0).hom (c σ) - gen X 0 σ)
            - ((singularChains ℤ X).d 1 0).hom ((theta U V r 1).hom (c σ)) := by
        rw [pi_apply_eq U V r 1 (c σ), map_sub]
        abel
      rw [harg]
      have hkill : (pi U V r 0).hom
          (((singularChains ℤ X).d 1 0).hom ((theta U V r 1).hom (c σ))) = 0 :=
        pi_kills_small U V r hr1 0 (isSmallChain_d (theta_mem U V r 1 (c σ)))
      rw [map_sub, hkill, sub_zero]
      have h1 : (pi U V r 0).hom
          (gen X 0 σ - ((singularChains ℤ X).d 1 0) (c σ)) = 0 :=
        pi_kills_small U V r hr1 0 (hc σ)
      simp only [map_sub] at h1
      rw [map_sub]
      exact sub_eq_zero.mpr (sub_eq_zero.mp h1).symm

/-- **The induction step**: given the component `κ m` of the contraction (killing the small
chains, with the contraction equation in degree `m` on cycles of degree `m`), produce the next
component `κ (m+1)` with the corresponding properties. -/
theorem stepCyclesCore (U V : Set X) (r : ∀ n, (singularChains ℤ X).X n ⟶ (smallChains U V).X n)
    (hr1 : ∀ n, (smallToSing U V).f n ≫ r n = 𝟙 ((smallChains U V).X n))
    (hD : ∀ n (b : (singularChains ℤ X).X n),
      ((singularChains ℤ X).d n (n - 1)) b ∈ smallChainSubmodule U V (n - 1) →
      ∃ c : (singularChains ℤ X).X (n + 1),
        b - ((singularChains ℤ X).d (n + 1) n) c ∈ smallChainSubmodule U V n)
    (m : ℕ) (km : (singularChains ℤ X).X m ⟶ (singularChains ℤ X).X (m + 1))
    (hkill : ∀ c : (singularChains ℤ X).X m, IsSmallChain U V c → km.hom c = 0)
    (hcyc : ∀ z : (singularChains ℤ X).X m, ((singularChains ℤ X).d m (m - 1)).hom z = 0 →
      (pi U V r m).hom (((singularChains ℤ X).d (m + 1) m).hom (km.hom z) - z) = 0) :
    ∃ k : (singularChains ℤ X).X (m + 1) ⟶ (singularChains ℤ X).X (m + 2),
      (∀ c, IsSmallChain U V c → k.hom c = 0) ∧
      (k ≫ (r (m + 2) ≫ (smallToSing U V).f (m + 2)) = 0) ∧
      (∀ x : (singularChains ℤ X).X (m + 1),
        (pi U V r (m + 1)).hom ((Eterm (m + 1) k km).hom x) = 0) := by
  classical
  -- `∂ σ` is a cycle and `y σ = gen σ - km (∂ σ)` has small boundary
  let zf : Simplex X (m + 1) → (singularChains ℤ X).X m :=
    fun σ => ((singularChains ℤ X).d (m + 1) m).hom (gen X (m + 1) σ)
  let yf : Simplex X (m + 1) → (singularChains ℤ X).X (m + 1) :=
    fun σ => gen X (m + 1) σ - km.hom (zf σ)
  have hzcyc : ∀ σ : Simplex X (m + 1),
      ((singularChains ℤ X).d m (m - 1)).hom (zf σ) = 0 := by
    intro σ
    have h := congrArg (fun (g : (singularChains ℤ X).X (m + 1) ⟶ (singularChains ℤ X).X (m - 1)) =>
      g.hom (gen X (m + 1) σ))
      (HomologicalComplex.d_comp_d (singularChains ℤ X) (m + 1) m (m - 1))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply, zf] using h
  have hmem : ∀ σ : Simplex X (m + 1),
      ((singularChains ℤ X).d (m + 1) m).hom (yf σ) ∈ smallChainSubmodule U V m := by
    intro σ
    have h1 := hcyc (zf σ) (hzcyc σ)
    have hsmall : IsSmallChain U V
        (((singularChains ℤ X).d (m + 1) m).hom (km.hom (zf σ)) - zf σ) :=
      (small_iff_pi U V r hr1 m _).mpr h1
    have hy : ((singularChains ℤ X).d (m + 1) m).hom (yf σ)
        = -(((singularChains ℤ X).d (m + 1) m).hom (km.hom (zf σ)) - zf σ) := by
      dsimp only [yf, zf]
      rw [map_sub]
      abel
    rw [hy]
    exact (smallChainSubmodule U V m).neg_mem hsmall
  -- choose the fillers given by the exactness hypothesis
  let c : Simplex X (m + 1) → (singularChains ℤ X).X (m + 2) :=
    fun σ => Classical.choose (hD (m + 1) (yf σ) (hmem σ))
  have hc : ∀ σ : Simplex X (m + 1),
      yf σ - ((singularChains ℤ X).d (m + 2) (m + 1)) (c σ)
        ∈ smallChainSubmodule U V (m + 1) :=
    fun σ => Classical.choose_spec (hD (m + 1) (yf σ) (hmem σ))
  -- prescribe `k` on the generators
  let k : (singularChains ℤ X).X (m + 1) ⟶ (singularChains ℤ X).X (m + 2) :=
    genDesc (m + 1) (fun σ => if IsSmall U V σ then 0 else (pi U V r (m + 2)).hom (c σ))
  have hk : ∀ σ : Simplex X (m + 1),
      k.hom (gen X (m + 1) σ)
        = if IsSmall U V σ then 0 else (pi U V r (m + 2)).hom (c σ) :=
    fun σ => genDesc_gen (m + 1) _ σ
  refine ⟨k, ?_, ?_, ?_⟩
  · exact kills_small_of_gen_kills k (fun σ hσ => by rw [hk σ]; simp [hσ])
  · apply eq_of_gen (M := (singularChains ℤ X).X (m + 2))
    intro σ
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply]
    rw [hk σ]
    split_ifs with h
    · simp
    · exact pi_theta_apply U V r hr1 (m + 2) (c σ)
  · refine pi_comp_of_gen (U := U) (V := V) (r := r) (m + 1) (Eterm (m + 1) k km) ?_
    intro σ
    rw [Eterm_succ]
    simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_sub,
      LinearMap.sub_apply, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
      LinearMap.id_apply]
    rw [hk σ]
    split_ifs with h
    · -- `σ` small: `k (gen σ) = 0` and `km (∂ σ) = 0`
      have hzsmall : IsSmallChain U V (zf σ) :=
        isSmallChain_d (n := m + 1) (isSmallChain_gen h)
      have hkm0 : km.hom (zf σ) = 0 := hkill (zf σ) hzsmall
      have hgsmall : IsSmallChain U V (gen X (m + 1) σ) := isSmallChain_gen h
      rw [map_zero, zero_add, hkm0, zero_sub, map_neg,
        pi_kills_small U V r hr1 (m + 1) hgsmall, neg_zero]
    · -- `σ` not small: `k (gen σ) = π (c σ)`
      have harg : ((singularChains ℤ X).d (m + 2) (m + 1)).hom
              ((pi U V r (m + 2)).hom (c σ)) + km.hom (zf σ) - gen X (m + 1) σ
          = (((singularChains ℤ X).d (m + 2) (m + 1)).hom (c σ) - yf σ)
            - ((singularChains ℤ X).d (m + 2) (m + 1)).hom
                ((theta U V r (m + 2)).hom (c σ)) := by
        rw [pi_apply_eq U V r (m + 2) (c σ), map_sub]
        dsimp only [yf]
        abel
      rw [harg]
      have hkill2 : (pi U V r (m + 1)).hom
          (((singularChains ℤ X).d (m + 2) (m + 1)).hom
            ((theta U V r (m + 2)).hom (c σ))) = 0 :=
        pi_kills_small U V r hr1 (m + 1)
          (isSmallChain_d (theta_mem U V r (m + 2) (c σ)))
      rw [map_sub, hkill2, sub_zero]
      have h1 : (pi U V r (m + 1)).hom
          (yf σ - ((singularChains ℤ X).d (m + 2) (m + 1)) (c σ)) = 0 :=
        pi_kills_small U V r hr1 (m + 1) (hc σ)
      simp only [map_sub] at h1
      rw [map_sub]
      exact sub_eq_zero.mpr (sub_eq_zero.mp h1).symm

/-- The state in degree `0`. -/
noncomputable def baseState (U V : Set X)
    (r : ∀ n, (singularChains ℤ X).X n ⟶ (smallChains U V).X n)
    (hr1 : ∀ n, (smallToSing U V).f n ≫ r n = 𝟙 ((smallChains U V).X n))
    (hD : ∀ n (b : (singularChains ℤ X).X n),
      ((singularChains ℤ X).d n (n - 1)) b ∈ smallChainSubmodule U V (n - 1) →
      ∃ c : (singularChains ℤ X).X (n + 1),
        b - ((singularChains ℤ X).d (n + 1) n) c ∈ smallChainSubmodule U V n) :
    CState U V r 0 :=
  let w := baseStateCore U V r hr1 hD
  { km := Classical.choose w
    km1 := 0
    hkill := (Classical.choose_spec w).1
    hcompl := (Classical.choose_spec w).2.1
    hInv := (Classical.choose_spec w).2.2 }

/-- The induction step on states. -/
noncomputable def stepState (U V : Set X)
    (r : ∀ n, (singularChains ℤ X).X n ⟶ (smallChains U V).X n)
    (hr1 : ∀ n, (smallToSing U V).f n ≫ r n = 𝟙 ((smallChains U V).X n))
    (hD : ∀ n (b : (singularChains ℤ X).X n),
      ((singularChains ℤ X).d n (n - 1)) b ∈ smallChainSubmodule U V (n - 1) →
      ∃ c : (singularChains ℤ X).X (n + 1),
        b - ((singularChains ℤ X).d (n + 1) n) c ∈ smallChainSubmodule U V n)
    (m : ℕ) (s : CState U V r m) : CState U V r (m + 1) :=
  let w := stepCyclesCore U V r hr1 hD m s.km s.hkill
    (inv_cycles U V r m s.km s.km1 s.hInv)
  { km := Classical.choose w
    km1 := s.km
    hkill := (Classical.choose_spec w).1
    hcompl := (Classical.choose_spec w).2.1
    hInv := (Classical.choose_spec w).2.2 }

/-- The family of states, by recursion on the degree. -/
noncomputable def stateAll (U V : Set X)
    (r : ∀ n, (singularChains ℤ X).X n ⟶ (smallChains U V).X n)
    (hr1 : ∀ n, (smallToSing U V).f n ≫ r n = 𝟙 ((smallChains U V).X n))
    (hD : ∀ n (b : (singularChains ℤ X).X n),
      ((singularChains ℤ X).d n (n - 1)) b ∈ smallChainSubmodule U V (n - 1) →
      ∃ c : (singularChains ℤ X).X (n + 1),
        b - ((singularChains ℤ X).d (n + 1) n) c ∈ smallChainSubmodule U V n) :
    ∀ m, CState U V r m :=
  Nat.rec (baseState U V r hr1 hD) (fun m s => stepState U V r hr1 hD m s)

theorem stateAll_zero (U V : Set X)
    (r : ∀ n, (singularChains ℤ X).X n ⟶ (smallChains U V).X n)
    (hr1 : ∀ n, (smallToSing U V).f n ≫ r n = 𝟙 ((smallChains U V).X n))
    (hD : ∀ n (b : (singularChains ℤ X).X n),
      ((singularChains ℤ X).d n (n - 1)) b ∈ smallChainSubmodule U V (n - 1) →
      ∃ c : (singularChains ℤ X).X (n + 1),
        b - ((singularChains ℤ X).d (n + 1) n) c ∈ smallChainSubmodule U V n) :
    stateAll U V r hr1 hD 0 = baseState U V r hr1 hD := rfl

theorem stateAll_succ (U V : Set X)
    (r : ∀ n, (singularChains ℤ X).X n ⟶ (smallChains U V).X n)
    (hr1 : ∀ n, (smallToSing U V).f n ≫ r n = 𝟙 ((smallChains U V).X n))
    (hD : ∀ n (b : (singularChains ℤ X).X n),
      ((singularChains ℤ X).d n (n - 1)) b ∈ smallChainSubmodule U V (n - 1) →
      ∃ c : (singularChains ℤ X).X (n + 1),
        b - ((singularChains ℤ X).d (n + 1) n) c ∈ smallChainSubmodule U V n)
    (m : ℕ) :
    stateAll U V r hr1 hD (m + 1)
      = stepState U V r hr1 hD m (stateAll U V r hr1 hD m) := rfl

theorem stateAll_succ_km1 (U V : Set X)
    (r : ∀ n, (singularChains ℤ X).X n ⟶ (smallChains U V).X n)
    (hr1 : ∀ n, (smallToSing U V).f n ≫ r n = 𝟙 ((smallChains U V).X n))
    (hD : ∀ n (b : (singularChains ℤ X).X n),
      ((singularChains ℤ X).d n (n - 1)) b ∈ smallChainSubmodule U V (n - 1) →
      ∃ c : (singularChains ℤ X).X (n + 1),
        b - ((singularChains ℤ X).d (n + 1) n) c ∈ smallChainSubmodule U V n)
    (m : ℕ) :
    (stateAll U V r hr1 hD (m + 1)).km1 = (stateAll U V r hr1 hD m).km := rfl

end

end Ct


/-- **Existence of a contraction of the complement of the small chains.**

This is the homological input to the proof that the inclusion of the small chains is a chain
homotopy equivalence. -/
theorem existsSmallChainsContraction {X : TopCat} (U V : Set X)
    (r : ∀ n, (Work.Cohomology.singularChains ℤ X).X n ⟶ (Work.Cohomology.smallChains U V).X n)
    (hr1 : ∀ n, (Work.Cohomology.smallToSing U V).f n ≫ r n
      = 𝟙 ((Work.Cohomology.smallChains U V).X n))
    (hr2 : ∀ n (σ : Work.Cohomology.Simplex X n) (h : Work.Cohomology.IsSmall U V σ),
      ((Work.Cohomology.smallToSing U V).f n) ((r n) (Work.Cohomology.gen X n σ))
        = Work.Cohomology.gen X n σ)
    (hr3 : ∀ n (σ : Work.Cohomology.Simplex X n), ¬ Work.Cohomology.IsSmall U V σ →
      (r n) (Work.Cohomology.gen X n σ) = 0)
    (hD : ∀ n (b : (Work.Cohomology.singularChains ℤ X).X n),
      ((Work.Cohomology.singularChains ℤ X).d n (n - 1)) b
        ∈ Work.Cohomology.smallChainSubmodule U V (n - 1) →
      ∃ c : (Work.Cohomology.singularChains ℤ X).X (n + 1),
        b - ((Work.Cohomology.singularChains ℤ X).d (n + 1) n) c
          ∈ Work.Cohomology.smallChainSubmodule U V n) :
    ∃ κ : ∀ n, (Work.Cohomology.singularChains ℤ X).X n ⟶ (Work.Cohomology.singularChains ℤ X).X (n + 1),
      (∀ n, (r n ≫ (Work.Cohomology.smallToSing U V).f n) ≫ κ n = 0) ∧
      (∀ n, κ n ≫ (r (n + 1) ≫ (Work.Cohomology.smallToSing U V).f (n + 1)) = 0) ∧
      ((κ 0 ≫ (Work.Cohomology.singularChains ℤ X).d 1 0
          - 𝟙 ((Work.Cohomology.singularChains ℤ X).X 0)) ≫
        (𝟙 ((Work.Cohomology.singularChains ℤ X).X 0)
          - r 0 ≫ (Work.Cohomology.smallToSing U V).f 0) = 0) ∧
      (∀ n, (κ (n + 1) ≫ (Work.Cohomology.singularChains ℤ X).d (n + 2) (n + 1)
          + (Work.Cohomology.singularChains ℤ X).d (n + 1) n ≫ κ n
          - 𝟙 ((Work.Cohomology.singularChains ℤ X).X (n + 1))) ≫
        (𝟙 ((Work.Cohomology.singularChains ℤ X).X (n + 1))
          - r (n + 1) ≫ (Work.Cohomology.smallToSing U V).f (n + 1)) = 0) := by
  classical
  let kappa : ∀ n, (singularChains ℤ X).X n ⟶ (singularChains ℤ X).X (n + 1) :=
    fun n => (Ct.stateAll U V r hr1 hD n).km
  refine ⟨kappa, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [Ct.eq_zero_iff]
    intro x
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    exact (Ct.stateAll U V r hr1 hD n).hkill _
      (Ct.theta_mem U V r n x)
  · intro n
    exact (Ct.stateAll U V r hr1 hD n).hcompl
  · rw [Ct.eq_zero_iff]
    intro x
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    change (Ct.pi U V r 0).hom
      (((Ct.stateAll U V r hr1 hD 0).km ≫ (singularChains ℤ X).d 1 0
        - 𝟙 ((singularChains ℤ X).X 0)).hom x) = 0
    have hE : Ct.Eterm 0 (Ct.stateAll U V r hr1 hD 0).km (Ct.stateAll U V r hr1 hD 0).km1
        = ((Ct.stateAll U V r hr1 hD 0).km ≫ (singularChains ℤ X).d 1 0
            - 𝟙 ((singularChains ℤ X).X 0)) :=
      Ct.Eterm_zero _ _
    rw [← hE]
    exact (Ct.stateAll U V r hr1 hD 0).hInv x
  · intro n
    rw [Ct.eq_zero_iff]
    intro x
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    show (Ct.pi U V r (n+1)).hom
      (((Ct.stateAll U V r hr1 hD (n+1)).km ≫ (singularChains ℤ X).d (n + 2) (n + 1)
        + (singularChains ℤ X).d (n + 1) n ≫ (Ct.stateAll U V r hr1 hD n).km
        - 𝟙 ((singularChains ℤ X).X (n + 1))).hom x) = 0
    have hE : Ct.Eterm (n + 1) (Ct.stateAll U V r hr1 hD (n + 1)).km
          (Ct.stateAll U V r hr1 hD (n + 1)).km1
        = ((Ct.stateAll U V r hr1 hD (n+1)).km ≫ (singularChains ℤ X).d (n + 2) (n + 1)
            + (singularChains ℤ X).d (n + 1) n ≫ (Ct.stateAll U V r hr1 hD n).km
            - 𝟙 ((singularChains ℤ X).X (n + 1))) := by
      rw [Ct.stateAll_succ_km1]
      exact Ct.Eterm_succ n _ _
    rw [← hE]
    exact (Ct.stateAll U V r hr1 hD (n + 1)).hInv x

end Work.Cohomology
