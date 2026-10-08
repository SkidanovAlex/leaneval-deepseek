import Mathlib
import Submission.Work.Hering.AppVII.brauer_lift_aux
import Submission.Work.Hering.AppVII.brauer_central
import Submission.Work.Hering.AppVII.toK_properties
import Submission.Work.Hering.AppVII.brauer_setup
import Submission.Work.NormalComplement.AppVII.TildeEAux
import Submission.Work.NormalComplement.AppVII.LiftTildeECentral
import Submission.Work.NormalComplement.AppVII.LiftTildeEMulEqZero
import Submission.Work.NormalComplement.AppVII.LiftSumTildeE

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The uniqueness of the block of an irreducible coprime Brauer representation

Let `A` be a finite group, `r` a prime with `r ∤ |A|`, `k = F̄_r`, and `ρ` an irreducible
`k`-representation of `A`.  Then there is exactly one irreducible complex character `χ` of `A`
whose lifted central primitive idempotent `toK χ ∈ k[A]` acts as the identity on `ρ`.

We prove this from scratch, without using the as-yet-unproved upstream statements
`Work.Hering.AppVII.tildeE_*`, `toK_properties`, `existsUnique_toK_acts_one`:

* the four `ℤ[ζ_|A|][A]`-identities for the integral lifts `tildeE χ = |A| • e_χ` are available
  fully proved (`LiftTildeECentral`, `LiftTildeEMulEqZero`, `LiftSumTildeE`), and the remaining
  `|A|`-idempotent relation `tildeE χ * tildeE χ = |A| • tildeE χ` is *derived* from orthogonality
  plus the sum (`tildeE_mul_self`);
* pushing these through the ring homomorphism `MonoidAlgebra.mapRingHom A (jred r |A| _)` gives the
  four facts about `toK χ ∈ k[A]` needed for the argument: centrality, idempotence, orthogonality
  and `∑_χ toK χ = 1`;
* since each `ρ (toK χ)` is then a central idempotent, it is `0` or `1` (its kernel is a
  subrepresentation of the irreducible `ρ`), and the two constraints `∑_χ ρ (toK χ) = 1` and
  orthogonality pin down exactly one `χ`.
-/

noncomputable section

open Classical

open scoped BigOperators MonoidAlgebra

namespace Work.NormalComplement.AppVII

/-- `|A|` is nonzero in `k = F̄_r` when `r ∤ |A|`. -/
private theorem natCard_ne_zero_brauer {A : Type*} [Group A] [Fintype A] {r : ℕ} [Fact r.Prime]
    (hcop : Nat.Coprime r (Nat.card A)) :
    (Nat.card A : Work.Hering.AppVII.BrauerField r) ≠ 0 := by
  intro h
  exact Work.Hering.AppVII.not_dvd_card hcop
    ((CharP.cast_eq_zero_iff (Work.Hering.AppVII.BrauerField r) r (Nat.card A)).mp h)

/-- The map `jred` to the coefficient field, as a ring homomorphism of group algebras,
appears in the definition of `toK`; this is a definitional unfolding. -/
private theorem toK_eq {A : Type*} [Group A] [Fintype A] {r : ℕ} [Fact r.Prime]
    (hcop : Nat.Coprime r (Nat.card A)) (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A) :
    Work.Hering.AppVII.toK hcop χ hχ =
      (Nat.card A : Work.Hering.AppVII.BrauerField r)⁻¹ •
        (MonoidAlgebra.mapRingHom A (Work.Hering.AppVII.jred r (Nat.card A)
          (Work.Hering.AppVII.not_dvd_card hcop)))
          (Work.Hering.AppVII.tildeE χ hχ) := rfl

/-- **The `|A|`-idempotent relation for the integral lifts `tildeE`.**  It is derived from the
orthogonality `tildeE χ * tildeE χ' = 0` (`χ ≠ χ'`) together with `∑_χ tildeE χ = |A| • 1`. -/
private theorem tildeE_mul_self {A : Type*} [Group A] [Fintype A] (χ : A → ℂ)
    (hχ : χ ∈ Work.CharCore.Irr A) :
    Work.Hering.AppVII.tildeE χ hχ * Work.Hering.AppVII.tildeE χ hχ =
      (Nat.card A : Work.Hering.AppVII.CycloRing (Nat.card A)) •
        Work.Hering.AppVII.tildeE χ hχ := by
  have h := congrArg (fun z => Work.Hering.AppVII.tildeE χ hχ * z)
    (LiftSumTildeE (A := A))
  rw [Finset.mul_sum] at h
  rw [mul_smul_comm, mul_one] at h
  have hL : (∑ x ∈ (Work.CharCore.Irr A).attach,
      Work.Hering.AppVII.tildeE χ hχ * Work.Hering.AppVII.tildeE x.1 x.2)
      = Work.Hering.AppVII.tildeE χ hχ * Work.Hering.AppVII.tildeE χ hχ := by
    refine Finset.sum_eq_single_of_mem (⟨χ, hχ⟩ : ↥(Work.CharCore.Irr A)) ?_ ?_
    · exact Finset.mem_attach _ _
    · intro b _ hb
      exact LiftTildeEMulEqZero hχ b.2 (fun hc => hb (Subtype.ext hc.symm))
  rw [hL] at h
  exact h

/-- `toK χ` commutes with every basis element `single g 1` of `k[A]`. -/
private theorem toK_comm_single {A : Type*} [Group A] [Fintype A] {r : ℕ} [Fact r.Prime]
    (hcop : Nat.Coprime r (Nat.card A))
    (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A) (g : A) :
    MonoidAlgebra.single g (1 : Work.Hering.AppVII.BrauerField r) *
        Work.Hering.AppVII.toK hcop χ hχ =
      Work.Hering.AppVII.toK hcop χ hχ *
        MonoidAlgebra.single g (1 : Work.Hering.AppVII.BrauerField r) := by
  rw [toK_eq hcop χ hχ, mul_smul_comm, smul_mul_assoc]
  congr 1
  have hsingle : (MonoidAlgebra.mapRingHom A (Work.Hering.AppVII.jred r (Nat.card A)
        (Work.Hering.AppVII.not_dvd_card hcop)))
        (MonoidAlgebra.single g (1 : Work.Hering.AppVII.CycloRing (Nat.card A))) =
      MonoidAlgebra.single g (1 : Work.Hering.AppVII.BrauerField r) := by
    rw [MonoidAlgebra.mapRingHom_single, map_one]
  rw [← hsingle, ← map_mul, LiftTildeECentral χ hχ
      (MonoidAlgebra.single g (1 : Work.Hering.AppVII.CycloRing (Nat.card A))),
    map_mul, hsingle]

/-- `toK χ` is central in `k[A]`. -/
private theorem toK_central {A : Type*} [Group A] [Fintype A] {r : ℕ} [Fact r.Prime]
    (hcop : Nat.Coprime r (Nat.card A))
    (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A)
    (x : MonoidAlgebra (Work.Hering.AppVII.BrauerField r) A) :
    x * Work.Hering.AppVII.toK hcop χ hχ = Work.Hering.AppVII.toK hcop χ hχ * x := by
  induction x using MonoidAlgebra.induction_on with
  | of g => simpa [MonoidAlgebra.of_apply] using toK_comm_single hcop χ hχ g
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul c x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

/-- `toK χ` is an idempotent of `k[A]`. -/
private theorem toK_mul_self {A : Type*} [Group A] [Fintype A] {r : ℕ} [Fact r.Prime]
    (hcop : Nat.Coprime r (Nat.card A)) (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A) :
    Work.Hering.AppVII.toK hcop χ hχ * Work.Hering.AppVII.toK hcop χ hχ =
      Work.Hering.AppVII.toK hcop χ hχ := by
  have hnn := natCard_ne_zero_brauer hcop
  rw [toK_eq hcop χ hχ, smul_mul_assoc, mul_smul_comm, smul_smul,
    show (MonoidAlgebra.mapRingHom A (Work.Hering.AppVII.jred r (Nat.card A)
          (Work.Hering.AppVII.not_dvd_card hcop)))
          (Work.Hering.AppVII.tildeE χ hχ) *
        (MonoidAlgebra.mapRingHom A (Work.Hering.AppVII.jred r (Nat.card A)
          (Work.Hering.AppVII.not_dvd_card hcop)))
          (Work.Hering.AppVII.tildeE χ hχ) =
      (Nat.card A : Work.Hering.AppVII.BrauerField r) •
        (MonoidAlgebra.mapRingHom A (Work.Hering.AppVII.jred r (Nat.card A)
          (Work.Hering.AppVII.not_dvd_card hcop)))
          (Work.Hering.AppVII.tildeE χ hχ) from by
      rw [← map_mul, tildeE_mul_self χ hχ,
        Nat.cast_smul_eq_nsmul (Work.Hering.AppVII.CycloRing (Nat.card A)) (Nat.card A),
        map_nsmul,
        ← Nat.cast_smul_eq_nsmul (Work.Hering.AppVII.BrauerField r) (Nat.card A)],
    smul_smul, mul_assoc, inv_mul_cancel₀ hnn, mul_one]

/-- Distinct `toK χ` are orthogonal. -/
private theorem toK_mul_eq_zero {A : Type*} [Group A] [Fintype A] {r : ℕ} [Fact r.Prime]
    (hcop : Nat.Coprime r (Nat.card A))
    (χ χ' : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A) (hχ' : χ' ∈ Work.CharCore.Irr A)
    (hne : χ ≠ χ') :
    Work.Hering.AppVII.toK hcop χ hχ * Work.Hering.AppVII.toK hcop χ' hχ' = 0 := by
  rw [toK_eq hcop χ hχ, toK_eq hcop χ' hχ', smul_mul_assoc, mul_smul_comm, smul_smul,
    ← map_mul, LiftTildeEMulEqZero hχ hχ' hne, map_zero, smul_zero]

/-- The `toK χ` sum to `1` in `k[A]`. -/
private theorem toK_sum {A : Type*} [Group A] [Fintype A] {r : ℕ} [Fact r.Prime]
    (hcop : Nat.Coprime r (Nat.card A)) :
    Finset.sum (Work.CharCore.Irr A).attach
        (fun x => Work.Hering.AppVII.toK hcop x.1 x.2) = 1 := by
  have hnn := natCard_ne_zero_brauer hcop
  rw [show Finset.sum (Work.CharCore.Irr A).attach
        (fun x => Work.Hering.AppVII.toK hcop x.1 x.2) =
      Finset.sum (Work.CharCore.Irr A).attach
        (fun x => (Nat.card A : Work.Hering.AppVII.BrauerField r)⁻¹ •
          (MonoidAlgebra.mapRingHom A (Work.Hering.AppVII.jred r (Nat.card A)
            (Work.Hering.AppVII.not_dvd_card hcop)))
            (Work.Hering.AppVII.tildeE x.1 x.2)) from
    Finset.sum_congr rfl (fun x _ => toK_eq hcop x.1 x.2)]
  rw [← Finset.smul_sum, ← map_sum, LiftSumTildeE (A := A),
    Nat.cast_smul_eq_nsmul (Work.Hering.AppVII.CycloRing (Nat.card A)) (Nat.card A),
    map_nsmul,
    ← Nat.cast_smul_eq_nsmul (Work.Hering.AppVII.BrauerField r) (Nat.card A),
    map_one, smul_smul, inv_mul_cancel₀ hnn, one_smul]

/-- **A central idempotent endomorphism of an irreducible representation is `0` or `1`.**  Its
kernel is a subrepresentation, hence `⊥` or `⊤`; in the first case it is injective and idempotent,
in the second it vanishes. -/
private theorem idem_endo_eq_zero_or_one {k : Type*} [Field k] {A : Type*} [Group A]
    {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k A V) (hρ : ρ.IsIrreducible) (φ : Module.End k V)
    (hφ2 : φ * φ = φ) (hcomm : ∀ g : A, φ * ρ g = ρ g * φ) : φ = 0 ∨ φ = 1 := by
  haveI : IsSimpleOrder (Subrepresentation ρ) := hρ
  let W : Subrepresentation ρ :=
    ⟨LinearMap.ker φ, by
      intro g v hv
      rw [LinearMap.mem_ker] at hv ⊢
      have h2 := congrArg (fun f : Module.End k V => f v) (hcomm g)
      rw [Module.End.mul_apply, Module.End.mul_apply, hv, map_zero] at h2
      exact h2⟩
  have hWker : W.toSubmodule = LinearMap.ker φ := rfl
  rcases eq_bot_or_eq_top W with hW | hW
  · right
    have hker : LinearMap.ker φ = ⊥ := by rw [← hWker, hW]; rfl
    apply LinearMap.ext
    intro v
    have hv : v - φ v ∈ LinearMap.ker φ := by
      rw [LinearMap.mem_ker, map_sub]
      have h3 : φ (φ v) = φ v := by rw [← Module.End.mul_apply, hφ2]
      rw [h3, sub_self]
    rw [hker, Submodule.mem_bot] at hv
    show φ v = v
    exact (sub_eq_zero.mp hv).symm
  · left
    have hker : LinearMap.ker φ = ⊤ := by rw [← hWker, hW]; rfl
    apply LinearMap.ext
    intro v
    have hv : v ∈ LinearMap.ker φ := by rw [hker]; exact Submodule.mem_top
    rw [LinearMap.mem_ker] at hv
    simpa using hv

/-- **The block of an irreducible coprime Brauer representation is unique.**  Stated with the
four properties of `toK` as hypotheses, so that it is reusable. -/
private theorem existsUnique_from_props {A : Type*} [Group A] [Fintype A] {r : ℕ} [Fact r.Prime]
    (hcop : Nat.Coprime r (Nat.card A))
    (hcent : ∀ (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A)
      (x : MonoidAlgebra (Work.Hering.AppVII.BrauerField r) A),
        x * Work.Hering.AppVII.toK hcop χ hχ = Work.Hering.AppVII.toK hcop χ hχ * x)
    (hidem : ∀ (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A),
        Work.Hering.AppVII.toK hcop χ hχ * Work.Hering.AppVII.toK hcop χ hχ =
          Work.Hering.AppVII.toK hcop χ hχ)
    (horth : ∀ (χ χ' : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A) (hχ' : χ' ∈ Work.CharCore.Irr A),
        χ ≠ χ' → Work.Hering.AppVII.toK hcop χ hχ * Work.Hering.AppVII.toK hcop χ' hχ' = 0)
    (hsum : Finset.sum (Work.CharCore.Irr A).attach
        (fun x => Work.Hering.AppVII.toK hcop x.1 x.2) = 1)
    {V : Type*} [AddCommGroup V] [Module (Work.Hering.AppVII.BrauerField r) V]
    [Module.Finite (Work.Hering.AppVII.BrauerField r) V]
    (ρ : Representation (Work.Hering.AppVII.BrauerField r) A V) (hρ : ρ.IsIrreducible) :
    ∃! χ : {χ : A → ℂ // χ ∈ Work.CharCore.Irr A},
      ρ.asAlgebraHom (Work.Hering.AppVII.toK hcop χ.1 χ.2) = 1 := by
  haveI : Nontrivial V := by
    haveI : IsSimpleModule (MonoidAlgebra (Work.Hering.AppVII.BrauerField r) A) ρ.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hρ
    haveI : Nontrivial ρ.asModule :=
      IsSimpleModule.nontrivial (MonoidAlgebra (Work.Hering.AppVII.BrauerField r) A) ρ.asModule
    exact Function.Injective.nontrivial ρ.asModuleEquiv.injective
  have hdisj : ∀ x : ↥(Work.CharCore.Irr A),
      ρ.asAlgebraHom (Work.Hering.AppVII.toK hcop x.1 x.2) = 0 ∨
      ρ.asAlgebraHom (Work.Hering.AppVII.toK hcop x.1 x.2) = 1 := by
    intro x
    refine idem_endo_eq_zero_or_one ρ hρ _ ?_ ?_
    · rw [← map_mul, hidem x.1 x.2]
    · intro g
      rw [← Representation.asAlgebraHom_of ρ g, ← map_mul, ← map_mul]
      rw [hcent x.1 x.2 (MonoidAlgebra.of (Work.Hering.AppVII.BrauerField r) A g)]
  have hsumφ : (∑ x ∈ (Work.CharCore.Irr A).attach,
      ρ.asAlgebraHom (Work.Hering.AppVII.toK hcop x.1 x.2)) = 1 := by
    rw [← map_sum, hsum, map_one]
  have hne0 : (∑ x ∈ (Work.CharCore.Irr A).attach,
      ρ.asAlgebraHom (Work.Hering.AppVII.toK hcop x.1 x.2)) ≠ 0 := by
    rw [hsumφ]; exact one_ne_zero
  obtain ⟨w, _, hwne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne0
  have hw : ρ.asAlgebraHom (Work.Hering.AppVII.toK hcop w.1 w.2) = 1 :=
    (hdisj w).resolve_left hwne
  refine ⟨w, hw, ?_⟩
  intro y hy
  by_contra hne
  have hyw : y.1 ≠ w.1 := fun h => hne (Subtype.ext h)
  exact one_ne_zero (by
    have h2 : ρ.asAlgebraHom (Work.Hering.AppVII.toK hcop y.1 y.2) *
        ρ.asAlgebraHom (Work.Hering.AppVII.toK hcop w.1 w.2) = 1 := by rw [hy, hw, one_mul]
    have h3 : ρ.asAlgebraHom (Work.Hering.AppVII.toK hcop y.1 y.2) *
        ρ.asAlgebraHom (Work.Hering.AppVII.toK hcop w.1 w.2) = 0 := by
      rw [← map_mul, horth y.1 w.1 y.2 w.2 hyw, map_zero]
    rw [← h2, h3])

theorem LiftExistsUniqueToK {A : Type*} [Group A] [Fintype A] {r : ℕ} [Fact r.Prime]
    (hcop : Nat.Coprime r (Nat.card A))
    {V : Type*} [AddCommGroup V] [Module (Work.Hering.AppVII.BrauerField r) V]
    [Module.Finite (Work.Hering.AppVII.BrauerField r) V]
    (ρ : Representation (Work.Hering.AppVII.BrauerField r) A V) (hρ : ρ.IsIrreducible) :
    ∃! χ : {χ : A → ℂ // χ ∈ Work.CharCore.Irr A},
      ρ.asAlgebraHom (Work.Hering.AppVII.toK hcop χ.1 χ.2) = 1 :=
  existsUnique_from_props hcop
    (fun χ hχ x => toK_central hcop χ hχ x)
    (fun χ hχ => toK_mul_self hcop χ hχ)
    (fun χ χ' hχ hχ' hne => toK_mul_eq_zero hcop χ χ' hχ hχ' hne)
    (toK_sum hcop) ρ hρ

end Work.NormalComplement.AppVII
