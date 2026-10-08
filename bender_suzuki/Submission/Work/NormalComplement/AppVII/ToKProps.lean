import Mathlib
import Submission.Work.Hering.AppVII.brauer_lift_aux
import Submission.Work.Hering.AppVII.iota_injective
import Submission.Work.CharCore.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The reduced idempotents `toK χ ∈ k[A]`

Assuming the five `ℤ[ζ_|A|][A]`-identities for the integral lifts
`tildeE χ = (χ(1) : ℤ[ζ_|A|]) • ∑_g charLift χ g⁻¹ • single g 1 = |A| • e_χ`
of the central primitive idempotents `e_χ` of `ℂ[A]`, the reductions

`toK hcop χ hχ = (|A| : k)⁻¹ • MonoidAlgebra.map (jred r |A| _) (tildeE χ hχ)`

to `k[A]`, where `k = F̄_r` and `r ∤ |A|`, are central idempotents, nonzero, pairwise
orthogonal, with sum `1`, and are fixed by `single z 1` whenever `χ z = χ 1`.

Everything is proved by pushing the `tildeE`-identities through the ring homomorphism
`psi hcop = MonoidAlgebra.map (jred r |A| _) : ℤ[ζ_|A|][A] → k[A]` and multiplying by
`|A|⁻¹ ∈ k`.
-/

namespace Work.NormalComplement.AppVII

open Classical

open scoped BigOperators

/-! ## Two generalities on `MonoidAlgebra` -/

/-- `MonoidAlgebra.map f` is semilinear over the coefficient homomorphism `f`. -/
theorem map_smul_base {R S G : Type*} [CommSemiring R] [CommSemiring S] [Monoid G]
    (f : R →+* S) (c : R) (x : MonoidAlgebra R G) :
    MonoidAlgebra.map (f : R →+ S) (c • x) = f c • MonoidAlgebra.map (f : R →+ S) x := by
  rw [Algebra.smul_def, Algebra.smul_def, MonoidAlgebra.map_mul]
  congr 1
  rw [show algebraMap R (MonoidAlgebra R G) c = MonoidAlgebra.single 1 c from by
        rw [MonoidAlgebra.coe_algebraMap]; rfl,
      show algebraMap S (MonoidAlgebra S G) (f c) = MonoidAlgebra.single 1 (f c) from by
        rw [MonoidAlgebra.coe_algebraMap]; simp]
  exact MonoidAlgebra.map_single (f : R →+ S) c 1

/-- An element of `k[G]` commuting with every basis element `single a 1` is central: the elements
`single a (1 : k)` span `k[G]` over `k`, and `k` is central in `k[G]`. -/
theorem central_of_commute_single {k G : Type*} [CommSemiring k] [Group G]
    (z : MonoidAlgebra k G)
    (h : ∀ a : G, MonoidAlgebra.single a (1 : k) * z = z * MonoidAlgebra.single a (1 : k))
    (x : MonoidAlgebra k G) : x * z = z * x := by
  have hx : x = ∑ a ∈ (x.coeff).support, x.coeff a • MonoidAlgebra.single a (1 : k) := by
    conv_lhs => rw [← MonoidAlgebra.sum_coeff_single x]
    rw [Finsupp.sum]
    exact Finset.sum_congr rfl fun a _ => by
      rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  rw [hx, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_mul_assoc, mul_smul_comm, h a]

/-! ## The reduction homomorphism `psi` -/

variable {A : Type*} [Group A] [Fintype A] {r : ℕ} [Fact r.Prime]

/-- The reduction `psi hcop = MonoidAlgebra.map (jred r |A| _) : ℤ[ζ_|A|][A] → k[A]` of the
integral group algebra to the group algebra over `k = F̄_r` (`r ∤ |A|`). -/
noncomputable def psi (hcop : Nat.Coprime r (Nat.card A)) :
    MonoidAlgebra (Work.Hering.AppVII.CycloRing (Nat.card A)) A →+*
      MonoidAlgebra (Work.Hering.AppVII.BrauerField r) A :=
  MonoidAlgebra.mapRingHom (M := A)
    (Work.Hering.AppVII.jred r (Nat.card A) (Work.Hering.AppVII.not_dvd_card hcop))

/-- `toK χ` is `|A|⁻¹ • psi (tildeE χ)`. -/
theorem toK_eq_psi (hcop : Nat.Coprime r (Nat.card A)) (χ : A → ℂ)
    (hχ : χ ∈ Work.CharCore.Irr A) :
    Work.Hering.AppVII.toK hcop χ hχ =
      (Nat.card A : Work.Hering.AppVII.BrauerField r)⁻¹ •
        psi hcop (Work.Hering.AppVII.tildeE χ hχ) := rfl

/-- `psi` is semilinear over `jred`. -/
theorem psi_smul (hcop : Nat.Coprime r (Nat.card A))
    (c : Work.Hering.AppVII.CycloRing (Nat.card A))
    (x : MonoidAlgebra (Work.Hering.AppVII.CycloRing (Nat.card A)) A) :
    psi hcop (c • x) =
      Work.Hering.AppVII.jred r (Nat.card A) (Work.Hering.AppVII.not_dvd_card hcop) c •
        psi hcop x :=
  map_smul_base (Work.Hering.AppVII.jred r (Nat.card A)
    (Work.Hering.AppVII.not_dvd_card hcop)) c x

/-- `psi (single a c) = single a (jred c)`. -/
theorem psi_single (hcop : Nat.Coprime r (Nat.card A)) (a : A)
    (c : Work.Hering.AppVII.CycloRing (Nat.card A)) :
    psi hcop (MonoidAlgebra.single a c) =
      MonoidAlgebra.single a (Work.Hering.AppVII.jred r (Nat.card A)
        (Work.Hering.AppVII.not_dvd_card hcop) c) := by
  simp only [psi, MonoidAlgebra.mapRingHom_single]

/-- `psi` fixes the basis elements `single a 1`. -/
theorem psi_single_one (hcop : Nat.Coprime r (Nat.card A)) (a : A) :
    psi hcop (MonoidAlgebra.single a (1 : Work.Hering.AppVII.CycloRing (Nat.card A))) =
      MonoidAlgebra.single a (1 : Work.Hering.AppVII.BrauerField r) := by
  rw [psi_single, map_one]

/-! ## The value of `charLift χ` at `1` and the expansion of `psi (tildeE χ)` -/

/-- `charLift χ hχ 1 = (irrDeg χ : ℤ[ζ_|A|])`: both sides have the same image under the injective
`iota`, namely `χ 1 = irrDeg χ`. -/
theorem charLift_one (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A) :
    Work.Hering.AppVII.charLift χ hχ 1 =
      (Work.CharCore.irrDeg χ : Work.Hering.AppVII.CycloRing (Nat.card A)) := by
  apply Work.Hering.AppVII.iota_injective
  rw [Work.Hering.AppVII.iota_charLift, map_natCast, Work.CharCore.irrDeg_spec hχ]

/-- The explicit expansion of the reduction of `tildeE χ`:
`psi (tildeE χ) = (irrDeg χ : k) • ∑ g, jred (charLift χ hχ g⁻¹) • single g 1`. -/
theorem psi_tildeE (hcop : Nat.Coprime r (Nat.card A)) (χ : A → ℂ)
    (hχ : χ ∈ Work.CharCore.Irr A) :
    psi hcop (Work.Hering.AppVII.tildeE χ hχ) =
      (Work.CharCore.irrDeg χ : Work.Hering.AppVII.BrauerField r) •
        ∑ g : A, Work.Hering.AppVII.jred r (Nat.card A)
            (Work.Hering.AppVII.not_dvd_card hcop)
            (Work.Hering.AppVII.charLift χ hχ g⁻¹) •
          MonoidAlgebra.single g (1 : Work.Hering.AppVII.BrauerField r) := by
  rw [Work.Hering.AppVII.tildeE, psi_smul, map_natCast, map_sum]
  refine congrArg (fun z : MonoidAlgebra (Work.Hering.AppVII.BrauerField r) A =>
    (Work.CharCore.irrDeg χ : Work.Hering.AppVII.BrauerField r) • z)
    (Finset.sum_congr rfl fun g _ => ?_)
  rw [psi_smul, psi_single_one]

/-- A natural number not divisible by `r` is nonzero in `k = F̄_r`, which has characteristic `r`. -/
theorem natCast_ne_zero_brauer {m : ℕ} (hm : ¬ r ∣ m) :
    (m : Work.Hering.AppVII.BrauerField r) ≠ 0 := fun h =>
  hm ((CharP.cast_eq_zero_iff (Work.Hering.AppVII.BrauerField r) r m).mp h)

/-- The coefficient of `1` in `toK χ` is `|A|⁻¹ · (irrDeg χ)²`. -/
theorem toK_coeff_one (hcop : Nat.Coprime r (Nat.card A)) (χ : A → ℂ)
    (hχ : χ ∈ Work.CharCore.Irr A) :
    (Work.Hering.AppVII.toK hcop χ hχ).coeff 1 =
      (Nat.card A : Work.Hering.AppVII.BrauerField r)⁻¹ *
        (Work.CharCore.irrDeg χ : Work.Hering.AppVII.BrauerField r) ^ 2 := by
  rw [toK_eq_psi, MonoidAlgebra.coeff_smul_apply, psi_tildeE,
    MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [show (1 : A)⁻¹ = 1 from inv_one, charLift_one, map_natCast]
  ring

/-! ## The main theorem -/

/-- **The reduced idempotents `toK χ ∈ k[A]` inherit the idempotent package.**

Assuming the five `ℤ[ζ_|A|][A]`-identities for `tildeE` (see `TildeEProps`), the elements
`toK hcop χ hχ = |A|⁻¹ • MonoidAlgebra.map (jred r |A| _) (tildeE χ hχ)` of `k[A] = F̄_r[A]`
(`r ∤ |A|`) are central idempotents, nonzero, pairwise orthogonal, sum to `1`, and are fixed by
`single z 1` whenever `χ z = χ 1`.

Proof: `ψ = MonoidAlgebra.map (jred r |A| _)` is multiplicative on the coefficient ring, with
`ψ (single a c) = single a (jred c)`; everything follows from the corresponding `tildeE` identity
by pushing through `ψ` and multiplying by `|A|⁻¹`: centrality only needs checking against the
basis elements `single a 1` (which commute with `ψ u` because they commute with `ψ x` for
`x = single a 1` by the tildeE identity); the idempotent relation uses
`ψ (tildeE χ · tildeE χ) = |A| • ψ (tildeE χ)` together with `|A|⁻¹·|A| = 1` in `k`; non-vanishing
follows from the coefficient of `1`: `(toK χ) 1 = |A|⁻¹ · (irrDeg χ)² ≠ 0`, because
`charLift χ hχ 1 = irrDeg χ` (both have the same image under the injective `iota`) and
`irrDeg χ ∣ Nat.card A` is not divisible by `r` (`irr_degree_dvd_card`). -/
theorem ToKProps {A : Type*} [Group A] [Fintype A] {r : ℕ} [Fact r.Prime]
    (hcop : Nat.Coprime r (Nat.card A))
    (htilde :
      (∀ (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A)
        (x : MonoidAlgebra (Work.Hering.AppVII.CycloRing (Nat.card A)) A),
          x * Work.Hering.AppVII.tildeE χ hχ = Work.Hering.AppVII.tildeE χ hχ * x) ∧
      (∀ (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A),
          Work.Hering.AppVII.tildeE χ hχ * Work.Hering.AppVII.tildeE χ hχ =
            (Nat.card A : Work.Hering.AppVII.CycloRing (Nat.card A)) •
              Work.Hering.AppVII.tildeE χ hχ) ∧
      (∀ (χ χ' : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A) (hχ' : χ' ∈ Work.CharCore.Irr A), χ ≠ χ' →
          Work.Hering.AppVII.tildeE χ hχ * Work.Hering.AppVII.tildeE χ' hχ' = 0) ∧
      (Finset.sum (Work.CharCore.Irr A).attach (fun x => Work.Hering.AppVII.tildeE x.1 x.2) =
          (Nat.card A : Work.Hering.AppVII.CycloRing (Nat.card A)) •
            (1 : MonoidAlgebra (Work.Hering.AppVII.CycloRing (Nat.card A)) A)) ∧
      (∀ (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A) (z : A), χ z = χ 1 →
          Work.Hering.AppVII.tildeE χ hχ *
            MonoidAlgebra.single z (1 : Work.Hering.AppVII.CycloRing (Nat.card A)) =
          Work.Hering.AppVII.tildeE χ hχ)) :
    (∀ (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A),
        Work.Hering.AppVII.IsCentralIdempotent (Work.Hering.AppVII.toK hcop χ hχ)) ∧
    (∀ (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A), Work.Hering.AppVII.toK hcop χ hχ ≠ 0) ∧
    (∀ (χ χ' : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A) (hχ' : χ' ∈ Work.CharCore.Irr A), χ ≠ χ' →
        Work.Hering.AppVII.toK hcop χ hχ * Work.Hering.AppVII.toK hcop χ' hχ' = 0) ∧
    (Finset.sum (Work.CharCore.Irr A).attach (fun x => Work.Hering.AppVII.toK hcop x.1 x.2) = 1) ∧
    (∀ (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A) (z : A), χ z = χ 1 →
        Work.Hering.AppVII.toK hcop χ hχ *
          MonoidAlgebra.single z (1 : Work.Hering.AppVII.BrauerField r) =
        Work.Hering.AppVII.toK hcop χ hχ) := by
  classical
  obtain ⟨hc, hidem, horth, hsum, hfix⟩ := htilde
  have hn0 : (Nat.card A : Work.Hering.AppVII.BrauerField r) ≠ 0 :=
    natCast_ne_zero_brauer (Work.Hering.AppVII.not_dvd_card hcop)
  have hAinv : (Nat.card A : Work.Hering.AppVII.BrauerField r)⁻¹ *
      (Nat.card A : Work.Hering.AppVII.BrauerField r) = 1 := inv_mul_cancel₀ hn0
  -- `psi (tildeE χ)` is central in `k[A]`: it commutes with every `single a 1`.
  have hpsi_central : ∀ (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A)
      (x : MonoidAlgebra (Work.Hering.AppVII.BrauerField r) A),
      x * psi hcop (Work.Hering.AppVII.tildeE χ hχ)
        = psi hcop (Work.Hering.AppVII.tildeE χ hχ) * x := by
    intro χ hχ
    refine central_of_commute_single _ (fun a => ?_)
    calc MonoidAlgebra.single a (1 : Work.Hering.AppVII.BrauerField r)
            * psi hcop (Work.Hering.AppVII.tildeE χ hχ)
        = psi hcop (MonoidAlgebra.single a (1 : Work.Hering.AppVII.CycloRing (Nat.card A)))
            * psi hcop (Work.Hering.AppVII.tildeE χ hχ) := by
          rw [psi_single_one]
      _ = psi hcop (MonoidAlgebra.single a (1 : Work.Hering.AppVII.CycloRing (Nat.card A))
            * Work.Hering.AppVII.tildeE χ hχ) :=
          (map_mul (psi hcop) _ _).symm
      _ = psi hcop (Work.Hering.AppVII.tildeE χ hχ
            * MonoidAlgebra.single a (1 : Work.Hering.AppVII.CycloRing (Nat.card A))) := by
          rw [hc χ hχ (MonoidAlgebra.single a (1 : Work.Hering.AppVII.CycloRing (Nat.card A)))]
      _ = psi hcop (Work.Hering.AppVII.tildeE χ hχ)
            * psi hcop (MonoidAlgebra.single a (1 : Work.Hering.AppVII.CycloRing (Nat.card A))) :=
          map_mul (psi hcop) _ _
      _ = psi hcop (Work.Hering.AppVII.tildeE χ hχ)
            * MonoidAlgebra.single a (1 : Work.Hering.AppVII.BrauerField r) := by
          rw [psi_single_one]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- central idempotents
    intro χ hχ
    refine ⟨?_, ?_⟩
    · -- idempotent
      show Work.Hering.AppVII.toK hcop χ hχ * Work.Hering.AppVII.toK hcop χ hχ =
        Work.Hering.AppVII.toK hcop χ hχ
      rw [toK_eq_psi, smul_mul_smul_comm, ← map_mul, hidem χ hχ, psi_smul, map_natCast,
        smul_smul, mul_assoc, hAinv, mul_one]
    · -- central
      intro x
      rw [toK_eq_psi, mul_smul_comm, smul_mul_assoc, hpsi_central χ hχ x]
  · -- nonzero
    intro χ hχ hzero
    have hcoeff := toK_coeff_one hcop χ hχ
    rw [hzero] at hcoeff
    have h0 : ((0 : MonoidAlgebra (Work.Hering.AppVII.BrauerField r) A).coeff 1) = 0 := by simp
    rw [h0] at hcoeff
    have hd0 : (Work.CharCore.irrDeg χ : Work.Hering.AppVII.BrauerField r) ≠ 0 :=
      natCast_ne_zero_brauer fun hd => (Work.Hering.AppVII.not_dvd_card hcop)
        (dvd_trans hd (Work.CharCore.irr_degree_dvd_card hχ))
    exact (mul_ne_zero (inv_ne_zero hn0) (by rw [pow_two]; exact mul_ne_zero hd0 hd0))
      hcoeff.symm
  · -- pairwise orthogonal
    intro χ χ' hχ hχ' hne
    rw [toK_eq_psi, toK_eq_psi, smul_mul_smul_comm, ← map_mul,
      horth χ χ' hχ hχ' hne, map_zero, smul_zero]
  · -- the `toK χ` sum to `1`
    have hpush : Finset.sum (Work.CharCore.Irr A).attach
          (fun x => Work.Hering.AppVII.toK hcop x.1 x.2)
        = (Nat.card A : Work.Hering.AppVII.BrauerField r)⁻¹ •
          psi hcop (Finset.sum (Work.CharCore.Irr A).attach
            (fun x => Work.Hering.AppVII.tildeE x.1 x.2)) := by
      simp only [toK_eq_psi]
      rw [← Finset.smul_sum, ← map_sum]
    rw [hpush, hsum, psi_smul, map_natCast, map_one, smul_smul, hAinv, one_smul]
  · -- fixed by `single z 1` whenever `χ z = χ 1`
    intro χ hχ z hz
    rw [toK_eq_psi, smul_mul_assoc, ← psi_single_one hcop z, ← map_mul, hfix χ hχ z hz]

end Work.NormalComplement.AppVII
