import Mathlib
import Submission.Work.ZassenhausSuzuki.Core
import Submission.Work.ZassenhausSuzuki.SzModelCoords
import Submission.Work.ZassenhausSuzuki.isTitsTheta_titsTheta
import Submission.Work.Models.Port.Sz.Borel
import Submission.Work.Models.Port.Sz.SuzukiCondition
import Submission.Work.Models.Port.Sz.Weyl

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `SuzukiFProp` is false: the coordinatisation `e` is only determined up to the torus `Λ`

The requested lemma

`Work.ZassenhausSuzuki.SuzukiFProp` says: in the coordinates of a coordinatisation
`e : Q ≃* A(GF(2^m), θ)` under which the two-point stabiliser `D = H ∩ H^t` acts through the
standard torus `Λ = h(Kˣ)` (that is the hypothesis `htorus`), the book's map `f`
(`FRel H t x y`, i.e. `t x t = m · t · y`) is the Suzuki map `τ = SzA.sigma θ`.

**It is false**, and the reason is that its hypothesis on `e` does not pin `e` down.  If `e` is
admissible then so is `h_μ ∘ e` for every `μ ∈ Kˣ` (the torus is abelian, so composing with
`h_μ` does not change the `D`-action in the new coordinates), while the conclusion is *not*
invariant under that twist: `σ ∘ h_μ = h_{μ⁻¹} ∘ σ`, so in the twisted coordinates the same
element `f(x)` is claimed to be both `σ(e x)` and `h_{μ⁻²}(σ(e x))`.  Since `f` is a single,
well-defined map on `Q^#` (`frel_unique`, proved in this area), `SuzukiFProp` therefore forces
`h_{μ⁻²} = id` on `A(K,θ)^#`, i.e. `μ = 1` — for *every* `μ ∈ Kˣ`.  It follows that
`SuzukiFProp` is inconsistent with the existence of an instance of its own hypothesis set
(`no_instance_of_suzukiFProp` below), and since an instance exists — the Suzuki group `Sz(8)`
with the Borel `B`, root group `O₂(B) ≅ A(GF(8), x ↦ x⁴)` and the Borel's torus action — the
lemma is refuted outright (`not_suzukiFProp`, where the instance is the literal model
`SzModel 1 ≤ GL(4, GF(8))` of `ChallengeDeps.lean`, whose Borel is a Zassenhaus split rank-one
configuration with the required torus-coordinatisation).

The mathematical content of `SuzukiFProp` is correct once the *existence* of `e` is part of the
conclusion (as in `IsSuzukiConfiguration`, where `e` and the `f`-formula are bundled, or in the
corrected form
`∀ e, TorusCoords … e → ∃ e', TorusCoords … e' ∧ ∀ x ≠ 1, FRel H t x (e'.symm (σ (e' x)))`):
the Suzuki map `τ` really is the book's `f` in *some* coordinatisation, and that is all that the
recognition step of the area (`suzukiCoreProp_of0`, `recognize_szModel`) consumes.

## Contents

* Layer 1: the torus algebra in Higman's group `A(K,θ) = SzA K θ` that drives the twist
  (`N_hLam`, `sigma_hLam`, `mul_theta_eq_one`, `hLam_eq_one`, `hLam_apply_zero_one`,
  `sigma_one_zero`, `exists_unit_ne_one`).
* Layer 2: `TorusCoords` (the hypothesis on `e`) and its invariance under the twist
  `e ↦ e.trans (hLamHom θ μ)` (`torusCoords_twist`).
* Layer 3: `no_instance_of_suzukiFProp` — `SuzukiFProp` implies that its own hypothesis set is
  unsatisfiable.
* Layer 4: the model instance.  `szBorelS_isZassenhaus` (the model `Sz(2^(2n+1))` is a
  Zassenhaus group), `torusCoords_szAEquivSzTwoGroupS` (the Borel's torus acts on the root
  group through `Λ` in the coordinates `A(GF(2^(2n+1)), titsTheta n)`), and the resulting
  unconditional refutation `not_suzukiFProp : ¬ SuzukiFProp`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

open Work.ZassenhausSuzuki.SzA

/-! ## Layer 1: the torus algebra in `A(K,θ)` -/

variable {K : Type*} [Field K] [CharP K 2] (θ : K ≃+* K)

/-- `N (h_λ x) = λ^{2+θ} · N x`: the Suzuki form `N` is multiplied by `λ^{2+θ}` under the
torus.  (In the notation used here `λ * θ λ * λ` is `λ^{2+θ}`.) -/
theorem N_hLam (hθ : IsTitsTheta θ) (lam : K) (x : SzA K θ) :
    N θ (hLam θ lam x) = lam * θ lam * lam * N θ x := by
  obtain ⟨a, b⟩ := x
  show (lam * a) * (lam * a) * θ (lam * a) + (lam * a) * (lam * θ lam * b)
      + θ (lam * θ lam * b) = lam * θ lam * lam * (a * a * θ a + a * b + θ b)
  simp only [map_mul, hθ.2]
  ring

/-- **`σ ∘ h_λ = h_{λ⁻¹} ∘ σ`**: the Suzuki map `τ` intertwines the torus action with the
inverse torus action.  This is the identity responsible for the failure of `SuzukiFProp`: the
conclusion `f = σ` is not invariant under `e ↦ h_μ ∘ e`. -/
theorem sigma_hLam (hθ : IsTitsTheta θ) (lam : Kˣ) (x : SzA K θ) :
    SzA.sigma θ (hLam θ (lam : K) x) = hLam θ (((lam⁻¹ : Kˣ) : K)) (SzA.sigma θ x) := by
  have hN := N_hLam θ hθ (lam : K) x
  have hlam0 : (lam : K) ≠ 0 := Units.ne_zero lam
  have hθlam0 : θ (lam : K) ≠ 0 := fun h => hlam0 (θ.injective (by simpa using h))
  ext <;>
    simp only [SzA.sigma_a, SzA.sigma_b, SzA.hLam_a, SzA.hLam_b, hN,
      Units.val_inv_eq_inv_val, map_inv₀, div_eq_mul_inv, mul_inv]
  · field_simp
  · field_simp

/-- In characteristic two with `θ² =` squaring, `ν · θ ν = 1` forces `ν = 1`. -/
theorem mul_theta_eq_one (hθ : IsTitsTheta θ) {ν : K} (h : ν * θ ν = 1) : ν = 1 := by
  have hν0 : ν ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h; exact one_ne_zero h.symm
  have hθν0 : θ ν ≠ 0 := fun hh => hν0 (θ.injective (by simpa using hh))
  have h2 : θ ν * ν ^ 2 = 1 := by
    have := congrArg θ h
    simpa [map_mul, hθ.2, map_one] using this
  have h4 : θ ν * ν ^ 2 = θ ν * ν := by
    rw [h2, mul_comm (θ ν) ν]; exact h.symm
  have h3 : ν ^ 2 = ν := mul_left_cancel₀ hθν0 h4
  have h5 : ν * (ν - 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.mp h5 with h6 | h6
  · exact absurd h6 hν0
  · exact sub_eq_zero.mp h6

/-- The torus is fixed-point free on `A(K,θ)^#`: `h_ν` fixes only the identity for `ν ≠ 1`. -/
theorem hLam_eq_one (hθ : IsTitsTheta θ) {ν : Kˣ} (hν : ν ≠ 1) {x : SzA K θ}
    (h : hLam θ (ν : K) x = x) : x = 1 := by
  obtain ⟨a, b⟩ := x
  have h1 : (ν : K) * a = a := by simpa [SzA.hLam] using congrArg SzA.a h
  have h2 : (ν : K) * θ (ν : K) * b = b := by simpa [SzA.hLam] using congrArg SzA.b h
  have ha : a = 0 := by
    have h3 : ((ν : K) - 1) * a = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd (Units.ext (sub_eq_zero.mp h4)) hν
    · exact h4
  subst ha
  by_cases hb : b = 0
  · subst hb; rfl
  · exfalso
    have h3 : (ν : K) * θ (ν : K) = 1 := by
      have h4 : ((ν : K) * θ (ν : K) - 1) * b = 0 := by linear_combination h2
      rcases mul_eq_zero.mp h4 with h5 | h5
      · exact sub_eq_zero.mp h5
      · exact absurd h5 hb
    exact hν (Units.ext (mul_theta_eq_one θ hθ h3))

/-- The torus acts on `(0,1) ∈ A(K,θ)` by `(0,1) ↦ (0, ν·θν)`. -/
theorem hLam_apply_zero_one (ν : Kˣ) :
    hLam θ (ν : K) (⟨0, 1⟩ : SzA K θ) = ⟨0, (ν : K) * θ (ν : K)⟩ := by
  ext <;> simp [SzA.hLam]

/-- `σ (1,0) = (0,1)`. -/
theorem sigma_one_zero : SzA.sigma θ (⟨1, 0⟩ : SzA K θ) = ⟨0, 1⟩ := by
  ext <;> simp [SzA.sigma, SzA.N]

/-- There is a non-identity element of `Kˣ`: otherwise `K = GF(2)` and `θ = 1`. -/
theorem exists_unit_ne_one (hθ : IsTitsTheta θ) : ∃ μ : Kˣ, μ ≠ 1 := by
  by_contra h
  push_neg at h
  refine hθ.1 (RingEquiv.ext fun x => ?_)
  show θ x = x
  rcases eq_or_ne x 0 with hx | hx
  · simp [hx]
  · have hx1 : x = 1 := by
      have := congrArg (fun u : Kˣ => (u : K)) (h (Units.mk0 x hx))
      simpa using this
    rw [hx1, map_one]

/-! ## Layer 2: the hypothesis on `e` and its invariance under the twist -/

variable {G : Type*} [Group G] {H Q : Subgroup G} {t : G}

/-- The hypothesis of `SuzukiFProp` on the coordinatisation `e : Q ≃* A(K,θ)`: the two-point
stabiliser `D = twoPoint H t` acts on `Q` through the standard torus `Λ = h(Kˣ)`, written in the
`e`-coordinates. -/
def TorusCoords (K : Type*) [Field K] (θ : K ≃+* K) (H Q : Subgroup G) (t : G)
    (e : Q ≃* SzA K θ) : Prop :=
  ∀ d : G, d ∈ twoPoint H t → ∃ lam : Kˣ, ∀ x : Q,
    ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧ e y = SzA.hLam θ (lam : K) (e x)

/-- **The twist is admissible.**  If `D` acts through `Λ` in the coordinates `e`, then it acts
through `Λ` in the coordinates `h_μ ∘ e` as well: `Λ` is abelian, so `h_μ` commutes with every
`h_λ`.  This is the (missing) rigidity that `SuzukiFProp` assumes on `e`. -/
theorem torusCoords_twist {K : Type*} [Field K] {θ : K ≃+* K} {e : Q ≃* SzA K θ}
    (h : TorusCoords K θ H Q t e) (μ : Kˣ) :
    TorusCoords K θ H Q t (e.trans (SzA.hLamHom θ μ)) := by
  intro d hd
  obtain ⟨lam, hlam⟩ := h d hd
  refine ⟨lam, fun x => ?_⟩
  obtain ⟨y, hy, hye⟩ := hlam x
  refine ⟨y, hy, ?_⟩
  simp only [MulEquiv.trans_apply, SzA.hLamHom_apply, hye]
  rw [← SzA.hLam_mul, ← SzA.hLam_mul, mul_comm (μ : K) (lam : K)]

/-! ## Layer 3: the refutation -/

open Work.RankOneUniqueness

/-- **`SuzukiFProp` is inconsistent with its own hypotheses.**  If `G` is a simple group with a
Zassenhaus split rank-one configuration whose root group is coordinated by `A(GF(2^m),θ)`
(`θ` Tits) through a torus-equivariant `e`, then `SuzukiFProp` is false: applying it to `e` and
to the equally admissible `h_μ ∘ e` (`μ ≠ 1`) and using the uniqueness of the book's map `f`
(`frel_unique`) forces `h_{μ⁻²} = id` on `A(K,θ)^#`, hence `μ = 1`. -/
theorem no_instance_of_suzukiFProp (hF : SuzukiFProp)
    (G : Type) [Group G] [Finite G] (hG : IsSimpleGroup G)
    (H Q : Subgroup G) (t : G) (hsplit : IsSplitRankOne H Q t) (hz : IsZassenhaus H)
    (m : ℕ) (θ : GaloisField 2 m ≃+* GaloisField 2 m) (hθ : IsTitsTheta θ)
    (e : Q ≃* SzA (GaloisField 2 m) θ)
    (htorus : TorusCoords (GaloisField 2 m) θ H Q t e) : False := by
  obtain ⟨μ, hμ⟩ := exists_unit_ne_one θ hθ
  set ν : (GaloisField 2 m)ˣ := μ⁻¹ * μ⁻¹ with hν
  have htorus' : TorusCoords (GaloisField 2 m) θ H Q t (e.trans (SzA.hLamHom θ μ)) :=
    torusCoords_twist htorus μ
  have c₁ := hF G hG H Q t hsplit hz m θ hθ e htorus
  have c₂ := hF G hG H Q t hsplit hz m θ hθ (e.trans (SzA.hLamHom θ μ)) htorus'
  set x₀ : Q := e.symm (⟨1, 0⟩ : SzA (GaloisField 2 m) θ) with hx₀
  have hx₀ne : x₀ ≠ 1 := by
    intro h
    have h1 : (e x₀ : SzA (GaloisField 2 m) θ) = 1 := by rw [h]; exact map_one e
    rw [hx₀, MulEquiv.apply_symm_apply] at h1
    have h2 : (1 : GaloisField 2 m) = 0 := by simpa using congrArg SzA.a h1
    exact one_ne_zero h2
  have h1 := c₁ x₀ hx₀ne
  have h2 := c₂ x₀ hx₀ne
  have huniq : (e.symm (SzA.sigma θ (e x₀)) : Q)
      = ((e.trans (SzA.hLamHom θ μ)).symm
          (SzA.sigma θ ((e.trans (SzA.hLamHom θ μ)) x₀)) : Q) :=
    Subtype.ext (frel_unique hsplit h1 h2 (e.symm _).2 ((e.trans (SzA.hLamHom θ μ)).symm _).2)
  have hEq : SzA.sigma θ (e x₀)
      = e ((e.trans (SzA.hLamHom θ μ)).symm
          (SzA.sigma θ ((e.trans (SzA.hLamHom θ μ)) x₀))) := by
    have := congrArg (fun q : Q => e q) huniq
    simpa using this
  have hR : e ((e.trans (SzA.hLamHom θ μ)).symm
        (SzA.sigma θ ((e.trans (SzA.hLamHom θ μ)) x₀)))
      = hLam θ (ν : GaloisField 2 m) (SzA.sigma θ (e x₀)) := by
    rw [MulEquiv.symm_trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    have hfsym : ((SzA.hLamHom θ μ) : MulAut (SzA (GaloisField 2 m) θ)).symm
        = SzA.hLamHom θ μ⁻¹ := map_inv (SzA.hLamHom θ) μ
    rw [hfsym, SzA.hLamHom_apply, SzA.hLamHom_apply]
    rw [sigma_hLam θ hθ μ (e x₀)]
    rw [← SzA.hLam_mul]
    rw [hν, Units.val_mul]
  have hfin : SzA.sigma θ (e x₀) = hLam θ (ν : GaloisField 2 m) (SzA.sigma θ (e x₀)) :=
    hEq.trans hR
  have hex : e x₀ = (⟨1, 0⟩ : SzA (GaloisField 2 m) θ) := by
    rw [hx₀, MulEquiv.apply_symm_apply]
  rw [hex] at hfin
  rw [sigma_one_zero, hLam_apply_zero_one] at hfin
  have hb : (ν : GaloisField 2 m) * θ (ν : GaloisField 2 m) = 1 :=
    (congrArg SzA.b hfin).symm
  have hν1 : ν = 1 := Units.ext (mul_theta_eq_one θ hθ hb)
  have hμ2 : μ * μ = 1 := by
    have hν1' : μ⁻¹ * μ⁻¹ = 1 := by rw [← hν]; exact hν1
    calc μ * μ = μ * μ * (μ⁻¹ * μ⁻¹) := by rw [hν1', mul_one]
      _ = 1 := by group
  have hval2 : ((μ : GaloisField 2 m)) ^ 2 = 1 := by
    have := congrArg (fun u : (GaloisField 2 m)ˣ => (u : GaloisField 2 m)) hμ2
    simpa [pow_two] using this
  have hμK : (μ : GaloisField 2 m) = 1 := by
    rcases sq_eq_one_iff.mp hval2 with h' | h'
    · exact h'
    · rw [h', CharTwo.neg_eq]
  exact hμ (Units.ext hμK)

/-! ## Layer 4: the model instance

`SzModel n = Sz(2^(2n+1))` is a simple Zassenhaus group with Borel `szBorelS n`, root group
`szTwoGroupS n` of order `2^(4n+2)` and Weyl element `szWgM n`; in the coordinates
`szAEquivSzTwoGroupS n : A(GF(2^(2n+1)), titsTheta n) ≃* szTwoGroupS n` the Borel's torus acts
through the standard torus `Λ`.  Hence `SuzukiFProp` fails on this instance. -/

section Model

open Submission.Sz

variable (n : ℕ)
lemma szPtWeyl_ne_szPtBase : szPtWeyl n ≠ szPtBase n := by
  intro h
  refine szWgM_notMem_szBorelS n ?_
  rwa [← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient] at h

lemma szTwoGroupS_smul_szPtBase (q : ↥(szTwoGroupS n)) :
    (q : SzModel n) • szPtBase n = szPtBase n := by
  rw [← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient]
  exact szTwoGroupS_le_szBorelS n q.2

lemma szSmulWeyl_injective {q₁ q₂ : SzModel n} (hq₁ : q₁ ∈ szTwoGroupS n)
    (hq₂ : q₂ ∈ szTwoGroupS n) (h : q₁ • szPtWeyl n = q₂ • szPtWeyl n) : q₁ = q₂ := by
  have hmem : q₂⁻¹ * q₁ ∈ szTwoGroupS n :=
    (szTwoGroupS n).mul_mem ((szTwoGroupS n).inv_mem hq₂) hq₁
  have hstab : q₂⁻¹ * q₁ ∈ MulAction.stabilizer (SzModel n) (szPtWeyl n) := by
    rw [MulAction.mem_stabilizer_iff]
    calc (q₂⁻¹ * q₁) • szPtWeyl n = q₂⁻¹ • (q₁ • szPtWeyl n) := by rw [mul_smul]
      _ = q₂⁻¹ • (q₂ • szPtWeyl n) := by rw [h]
      _ = szPtWeyl n := by rw [← mul_smul q₂⁻¹ q₂ (szPtWeyl n), inv_mul_cancel, one_smul]
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj (szWgM n) (szPtBase n),
    MulAction.stabilizer_quotient] at hstab
  have hbot : q₂⁻¹ * q₁ ∈ (⊥ : Subgroup (SzModel n)) := by
    rw [← szTwoGroupS_inf_map_conj_eq_bot n (szWgM_notMem_szBorelS n)]
    exact ⟨hmem, hstab⟩
  have h1 : q₂⁻¹ * q₁ = 1 := Subgroup.mem_bot.mp hbot
  have h3 : q₁ = q₂ := by
    have h4 : q₂ * (q₂⁻¹ * q₁) = q₂ := by rw [h1, mul_one]
    rwa [← mul_assoc, mul_inv_cancel, one_mul] at h4
  exact h3

lemma szTS_conj_szTwoGroupS_mem {t u : SzModel n} (ht : t ∈ szTS n)
    (hu : u ∈ szTwoGroupS n) : t * u * t⁻¹ ∈ szTwoGroupS n :=
  (Subgroup.le_normalizer_iff.mp (szTS_le_normalizer_szTwoGroupS n)) t ht u hu

lemma szTS_mul_fixes_szPtWeyl {t : SzModel n} (ht : t ∈ szTS n) :
    t • szPtWeyl n = szPtWeyl n := szTS_fixes_szPtWeyl n t ht

lemma szSmulWeyl_act (q : ↥(szTwoGroupS n)) {t : SzModel n} (ht : t ∈ szTS n)
    (u : ↥(szTwoGroupS n)) :
    ((q : SzModel n) * t) • ((u : SzModel n) • szPtWeyl n)
      = ((q : SzModel n) * (t * (u : SzModel n) * t⁻¹)) • szPtWeyl n := by
  have h1 : (t * (u : SzModel n) * t⁻¹) * t = t * (u : SzModel n) := by group
  calc ((q : SzModel n) * t) • ((u : SzModel n) • szPtWeyl n)
      = (q : SzModel n) • (t • ((u : SzModel n) • szPtWeyl n)) := by rw [mul_smul]
    _ = (q : SzModel n) • ((t * (u : SzModel n)) • szPtWeyl n) := by
          rw [mul_smul t (u : SzModel n) (szPtWeyl n)]
    _ = (q : SzModel n) • ((t * (u : SzModel n) * t⁻¹) • (t • szPtWeyl n)) := by
          congr 1
          rw [← mul_smul (t * (u : SzModel n) * t⁻¹) t (szPtWeyl n), h1]
    _ = (q : SzModel n) • ((t * (u : SzModel n) * t⁻¹) • szPtWeyl n) := by
          rw [szTS_fixes_szPtWeyl n t ht]
    _ = ((q : SzModel n) * (t * (u : SzModel n) * t⁻¹)) • szPtWeyl n := by
          rw [mul_smul (q : SzModel n) (t * (u : SzModel n) * t⁻¹) (szPtWeyl n)]

lemma szTS_conj_ne_of_ne (hn : 1 ≤ n) {t : SzModel n} (ht : t ∈ szTS n) (ht1 : t ≠ 1)
    (u : ↥(szTwoGroupS n)) (hu : u ≠ 1) :
    t * (u : SzModel n) * t⁻¹ ≠ (u : SzModel n) := by
  intro hconj
  obtain ⟨x, hx⟩ : ∃ x : (SzField n)ˣ, szTg n x = (t : GL (Fin 4) (SzField n)) :=
    MonoidHom.mem_range.mp (Subgroup.mem_subgroupOf.mp ht)
  obtain ⟨a, b, hab⟩ : ∃ a b : SzField n, szUg n a b = (u : GL (Fin 4) (SzField n)) := by
    obtain ⟨a, b, h⟩ := (show ∃ a b : SzField n,
      (u : GL (Fin 4) (SzField n)) = szUg n a b from Subgroup.mem_subgroupOf.mp u.2)
    exact ⟨a, b, h.symm⟩
  have hx1 : x ≠ 1 := by
    intro h
    refine ht1 (Subtype.ext ?_)
    rw [← hx, h, szTg_one]
    rfl
  have hu1 : ¬ ((a, b) = (0, 0)) := by
    intro h0
    have ha0 : a = 0 := congrArg Prod.fst h0
    have hb0 : b = 0 := congrArg Prod.snd h0
    refine hu (Subtype.ext (Subtype.ext ?_))
    rw [← hab, ha0, hb0, szUg_zero]
    rfl
  have hGL : szUg n ((x : SzField n) * a) ((x : SzField n) ^ (1 + 2 ^ (n + 1)) * b)
      = szUg n a b := by
    have h' := congrArg (fun z : SzModel n => (z : GL (Fin 4) (SzField n))) hconj
    rw [show ((t * (u : SzModel n) * t⁻¹ : SzModel n) : GL (Fin 4) (SzField n))
        = (t : GL (Fin 4) (SzField n)) * (u : GL (Fin 4) (SzField n))
            * (t : GL (Fin 4) (SzField n))⁻¹ from rfl] at h'
    rw [← hx, ← hab, szTg_conj_szUg] at h'
    exact h'
  have hpair : ((x : SzField n) * a, (x : SzField n) ^ (1 + 2 ^ (n + 1)) * b) = (a, b) :=
    szUg_injective n hGL
  have ha : a = 0 := by
    have h1 : (x : SzField n) * a = a := by
      have := congrArg Prod.fst hpair
      simpa using this
    have h1' : ((x : SzField n) - 1) * a = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h1' with h2 | h2
    · exact absurd (Units.ext (sub_eq_zero.mp h2)) hx1
    · exact h2
  have hb : b = 0 := by
    have hb0 : b ≠ 0 := fun hb0 => hu1 (Prod.ext ha hb0)
    have h2 : (x : SzField n) ^ (1 + 2 ^ (n + 1)) * b = b := by
      have := congrArg Prod.snd hpair
      simpa using this
    have h2' : ((x : SzField n) ^ (1 + 2 ^ (n + 1)) - 1) * b = 0 := by linear_combination h2
    rcases mul_eq_zero.mp h2' with h3 | h3
    · have hxθ : (x : SzField n) * titsTheta n (x : SzField n) = 1 := by
        rw [← sub_eq_zero.mp h3]
        conv_rhs => rw [Nat.add_comm 1 (2 ^ (n + 1)), pow_succ']
        rw [titsTheta_apply]
      exact absurd (Units.ext (mul_theta_eq_one (titsTheta n) (isTitsTheta_titsTheta n hn) hxθ))
        hx1
    · exact h3
  exact hu1 (Prod.ext ha hb)

theorem szBorelS_isZassenhaus (hn : 1 ≤ n) :
    IsZassenhaus (szBorelS n) := by
  intro a b c hab hac hbc g ha hb hc
  obtain ⟨h, hha, hhb⟩ : ∃ h : SzModel n, h • a = szPtBase n ∧ h • b = szPtWeyl n := by
    by_cases ha0 : a = szPtBase n
    · obtain ⟨u, hu⟩ := szTwoGroupS_exists_smul_eq_of_ne n hn (x := b) (y := szPtWeyl n)
        (fun hh => hab (ha0.trans hh.symm)) (szPtWeyl_ne_szPtBase n)
      exact ⟨u, by rw [ha0]; exact szTwoGroupS_smul_szPtBase n u, hu⟩
    · obtain ⟨u₀, hu₀⟩ := szTwoGroupS_exists_smul_eq_of_ne n hn (szPtWeyl_ne_szPtBase n) ha0
      have h1a : (szWgM n * (u₀ : SzModel n)⁻¹) • a = szPtBase n := by
        rw [← hu₀]
        calc (szWgM n * (u₀ : SzModel n)⁻¹) • ((u₀ : SzModel n) • szPtWeyl n)
            = ((szWgM n * (u₀ : SzModel n)⁻¹) * (u₀ : SzModel n)) • szPtWeyl n := by
                rw [← mul_smul (szWgM n * (u₀ : SzModel n)⁻¹) (u₀ : SzModel n) (szPtWeyl n)]
          _ = szWgM n • szPtWeyl n := by rw [mul_assoc, inv_mul_cancel, mul_one]
          _ = szPtBase n := by
                rw [szPtWeyl, ← mul_smul (szWgM n) (szWgM n) (szPtBase n), szWgM_mul_self,
                  one_smul]
      have h1bne : (szWgM n * (u₀ : SzModel n)⁻¹) • b ≠ szPtBase n := by
        intro hh
        refine hab ?_
        have h2 : b = a := by
          have h3 := congrArg (fun z => (szWgM n * (u₀ : SzModel n)⁻¹)⁻¹ • z)
            (hh.trans h1a.symm)
          simpa using h3
        exact h2.symm
      obtain ⟨v, hv⟩ := szTwoGroupS_exists_smul_eq_of_ne n hn
        (x := (szWgM n * (u₀ : SzModel n)⁻¹) • b) (y := szPtWeyl n) h1bne
        (szPtWeyl_ne_szPtBase n)
      refine ⟨(v : SzModel n) * (szWgM n * (u₀ : SzModel n)⁻¹), ?_, ?_⟩
      · rw [mul_smul, h1a, szTwoGroupS_smul_szPtBase n v]
      · rw [mul_smul, hv]
  set g' : SzModel n := h * g * h⁻¹ with hg'
  have hia : h⁻¹ • szPtBase n = a := by
    rw [← hha, ← mul_smul h⁻¹ h a, inv_mul_cancel, one_smul]
  have hib : h⁻¹ • szPtWeyl n = b := by
    rw [← hhb, ← mul_smul h⁻¹ h b, inv_mul_cancel, one_smul]
  have hga : g' • szPtBase n = szPtBase n := by
    rw [hg', mul_smul, mul_smul, hia, ha, hha]
  have hgb : g' • szPtWeyl n = szPtWeyl n := by
    rw [hg', mul_smul, mul_smul, hib, hb, hhb]
  have hgc : g' • (h • c) = h • c := by
    rw [hg', mul_smul, mul_smul, inv_smul_smul, hc]
  have hg'B : g' ∈ szBorelS n := by
    have hmem : g' ∈ MulAction.stabilizer (SzModel n) (szPtBase n) :=
      MulAction.mem_stabilizer_iff.mpr hga
    rwa [show szPtBase n = ((1 : SzModel n) : SzModel n ⧸ szBorelS n) from rfl,
      MulAction.stabilizer_quotient] at hmem
  have hg'B' : g' ∈ szTwoGroupS n ⊔ szTS n := by rwa [szBorelS_eq_sup n] at hg'B
  obtain ⟨q, hq, t, ht, hqt⟩ := Submission.PSU3.mem_sup_mul (szTwoGroupS n) (szTS n)
    (szTS_le_normalizer_szTwoGroupS n) hg'B'
  have hq1 : q = 1 := by
    have h2 : (q : SzModel n) • szPtWeyl n = szPtWeyl n := by
      have h := hgb
      rw [hqt, mul_smul, szTS_fixes_szPtWeyl n t ht] at h
      exact h
    exact szSmulWeyl_injective n hq ((szTwoGroupS n).one_mem) (by rw [h2, one_smul])
  have hgt : g' = t := by
    rw [hqt, hq1]
    simp
  have hcbase : h • c ≠ szPtBase n := by
    intro hh
    have h2 : a = c := by
      have h3 := congrArg (fun z => h⁻¹ • z) hh
      rw [inv_smul_smul, hia] at h3
      exact h3.symm
    exact hac h2
  have hcweyl : h • c ≠ szPtWeyl n := by
    intro hh
    have h2 : b = c := by
      have h3 := congrArg (fun z => h⁻¹ • z) hh
      rw [inv_smul_smul, hib] at h3
      exact h3.symm
    exact hbc h2
  obtain ⟨u₃, hu₃⟩ := szTwoGroupS_exists_smul_eq_of_ne n hn hcbase (szPtWeyl_ne_szPtBase n)
  have hu₃1 : u₃ ≠ 1 := by
    intro h1
    refine hcweyl ?_
    rw [← hu₃, h1]
    simp
  have htfix : t * (u₃ : SzModel n) * t⁻¹ = (u₃ : SzModel n) := by
    have hfix : t • (h • c) = h • c := by
      rw [← hgt]; exact hgc
    have hunit : (u₃ : SzModel n)⁻¹ • szPtWeyl n = h • c := by
      rw [← hu₃, ← mul_smul (u₃ : SzModel n)⁻¹ (u₃ : SzModel n) (h • c), inv_mul_cancel,
        one_smul]
    have h3 : t • ((u₃ : SzModel n)⁻¹ • szPtWeyl n) = (u₃ : SzModel n)⁻¹ • szPtWeyl n := by
      rw [hunit]; exact hfix
    have h4 : ((t * (u₃ : SzModel n)⁻¹ * t⁻¹) : SzModel n) • szPtWeyl n
        = ((u₃ : SzModel n)⁻¹) • szPtWeyl n := by
      calc (t * (u₃ : SzModel n)⁻¹ * t⁻¹) • szPtWeyl n
          = t • ((u₃ : SzModel n)⁻¹ • (t⁻¹ • szPtWeyl n)) := by rw [mul_smul, mul_smul]
        _ = t • ((u₃ : SzModel n)⁻¹ • szPtWeyl n) := by
              rw [szTS_fixes_szPtWeyl n t⁻¹ ((szTS n).inv_mem ht)]
        _ = (u₃ : SzModel n)⁻¹ • szPtWeyl n := h3
    have h5 : (t * (u₃ : SzModel n)⁻¹ * t⁻¹) = (u₃ : SzModel n)⁻¹ :=
      szSmulWeyl_injective n
        (szTS_conj_szTwoGroupS_mem n ht ((szTwoGroupS n).inv_mem u₃.2))
        ((szTwoGroupS n).inv_mem u₃.2) h4
    have h6 := congrArg (fun z : SzModel n => z⁻¹) h5
    simpa [mul_inv_rev, inv_inv, mul_assoc] using h6
  have ht1 : t = 1 := by
    by_contra htne
    exact szTS_conj_ne_of_ne n hn ht htne u₃ hu₃1 htfix
  have hg1 : h * g * h⁻¹ = 1 := by rw [← hg', hgt, ht1]
  have := congrArg (fun z : SzModel n => h⁻¹ * z * h) hg1
  simpa [mul_assoc] using this
lemma subgroupOfEquivOfLe_symm_coe {G : Type*} [Group G] {H K : Subgroup G} (h : H ≤ K) (y : H) :
    ((((Subgroup.subgroupOfEquivOfLe h).symm y : ↥(H.subgroupOf K))) : G) = (y : G) := rfl

lemma szAEquivSzTwoGroupS_val (a b : SzField n) :
    ((szAEquivSzTwoGroupS n (⟨a, b⟩ : SzA (SzField n) (titsTheta n)) : ↥(szTwoGroupS n))
        : GL (Fin 4) (SzField n)) = szUg n a b := by
  show ((((szAEquivSzTwoGroup n).trans
        (Subgroup.subgroupOfEquivOfLe (szTwoGroup_le_szModel n)).symm)
        (⟨a, b⟩ : SzA (SzField n) (titsTheta n)) : ↥((szTwoGroup n).subgroupOf (SzModel n)))
      : GL (Fin 4) (SzField n)) = szUg n a b
  rw [MulEquiv.trans_apply, subgroupOfEquivOfLe_symm_coe]
  change ((szAMonoidHom n (⟨a, b⟩ : SzA (SzField n) (titsTheta n)) : szTwoGroup n)
      : GL (Fin 4) (SzField n)) = szUg n a b
  rfl

lemma szAEquivSzTwoGroupS_val' (x : SzA (SzField n) (titsTheta n)) :
    ((szAEquivSzTwoGroupS n x : ↥(szTwoGroupS n)) : GL (Fin 4) (SzField n))
      = szUg n x.a x.b := by
  have h : x = (⟨x.a, x.b⟩ : SzA (SzField n) (titsTheta n)) := rfl
  rw [h]
  exact szAEquivSzTwoGroupS_val n x.a x.b

lemma twoPoint_szBorelS :
    twoPoint (szBorelS n) (szWgM n) = szTS n :=
  szBorelS_inf_map_conj_eq n
theorem torusCoords_szAEquivSzTwoGroupS :
    TorusCoords (GaloisField 2 (2 * n + 1)) (titsTheta n)
      (szBorelS n) (szTwoGroupS n) (szWgM n) (szAEquivSzTwoGroupS n).symm := by
  intro d hd
  have hdT : d ∈ szTS n := by
    rwa [twoPoint_szBorelS n] at hd
  obtain ⟨x₀, hx₀⟩ := hdT
  have hx₀GL : (d : GL (Fin 4) (SzField n)) = szTg n x₀ := hx₀.symm
  refine ⟨x₀, fun x => ?_⟩
  set z : SzA (SzField n) (titsTheta n) := (szAEquivSzTwoGroupS n).symm x with hz
  have hxz : szAEquivSzTwoGroupS n z = x := by rw [hz, MulEquiv.apply_symm_apply]
  refine ⟨szAEquivSzTwoGroupS n (SzA.hLam (titsTheta n) (x₀ : SzField n) z), ?_, ?_⟩
  · apply Subtype.ext
    show ((szAEquivSzTwoGroupS n (SzA.hLam (titsTheta n) (x₀ : SzField n) z) : ↥(szTwoGroupS n))
        : GL (Fin 4) (SzField n)) = _
    rw [szAEquivSzTwoGroupS_val']
    rw [show ((d * x * d⁻¹ : SzModel n) : GL (Fin 4) (SzField n))
          = (d : GL (Fin 4) (SzField n)) * (x : GL (Fin 4) (SzField n))
              * (d : GL (Fin 4) (SzField n))⁻¹ from rfl]
    rw [show ((x : ↥(szTwoGroupS n)) : GL (Fin 4) (SzField n)) = szUg n z.a z.b from by
      rw [← hxz]; exact szAEquivSzTwoGroupS_val' n z]
    rw [hx₀GL, szTg_conj_szUg]
    have hθ : (x₀ : SzField n) * titsTheta n (x₀ : SzField n)
        = (x₀ : SzField n) ^ (1 + 2 ^ (n + 1)) := by
      conv_rhs => rw [Nat.add_comm 1 (2 ^ (n + 1)), pow_succ']
      rw [titsTheta_apply]
    rw [SzA.hLam_a, SzA.hLam_b, hθ]
  · rw [MulEquiv.symm_apply_apply, hz]

end Model

/-- **`SuzukiFProp` is FALSE.**  It is refuted by the literal Suzuki group `Sz(8) = SzModel 1`:
with `B = szBorelS 1` the Borel, `Q = szTwoGroupS 1` its (Suzuki) Sylow `2`-subgroup,
`t = szWgM 1` and the coordinates `e = (szAEquivSzTwoGroupS 1).symm`, all the hypotheses of
`SuzukiFProp` hold (`m = 3`, `θ = titsTheta 1`), while the two admissible coordinatisations `e`
and `h_μ ∘ e` (`μ ≠ 1`) demand two different values of the book's map `f`. -/
theorem not_suzukiFProp : ¬ SuzukiFProp := by
  intro hF
  haveI : Finite (SzModel 1) := Subtype.finite
  exact no_instance_of_suzukiFProp hF (SzModel 1) (Submission.Sz.isSimpleGroup_SzModel 1 le_rfl)
    (Submission.Sz.szBorelS 1) (Submission.Sz.szTwoGroupS 1) (Submission.Sz.szWgM 1)
    (szSplitRankOne 1 le_rfl) (szBorelS_isZassenhaus 1 le_rfl) 3 (titsTheta 1)
    (isTitsTheta_titsTheta 1 le_rfl) (szAEquivSzTwoGroupS 1).symm
    (torusCoords_szAEquivSzTwoGroupS 1)

-- The requested statement `theorem suzukiFProp : SuzukiFProp` is **false** (see
-- `not_suzukiFProp : ¬ SuzukiFProp` above, an unconditional refutation): the two admissible
-- coordinatisations `e` and `h_μ ∘ e` (`μ ≠ 1`) of the Borel of `Sz(8) = SzModel 1` demand two
-- different values of the book's map `f`.  There is therefore no proof to be given, and the
-- statement was replaced by `SuzukiCoordsProp` (`CoreV3.lean`, proved to be the right socket by
-- `suzukiCoreProp_of_coords`), in which the existence of the good coordinatisation `e'` is part
-- of the conclusion.

end Work.ZassenhausSuzuki
