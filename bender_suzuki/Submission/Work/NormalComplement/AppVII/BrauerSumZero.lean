import Mathlib
import Submission.Work.Hering.AppVII.brauer_lift_aux
import Submission.Work.Hering.AppVII.brauer_setup
import Submission.Work.Hering.AppVII.brauer_central
import Submission.Work.CharCore.Main
import Submission.Work.CharCore.column_orthogonality_conj
import Submission.Work.NormalComplement.AppVII.MapIotaTildeE
import Submission.Work.NormalComplement.AppVII.BlockInjectivePrim
import Submission.Work.NormalComplement.AppVII.ToKPrimitive
import Submission.Work.NormalComplement.AppVII.RhoCTildeE

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement.AppVII

noncomputable section

open Classical MonoidAlgebra
open scoped BigOperators MonoidAlgebra

/-- `|A|` is non-zero in `k = F̄_r` when `r ∤ |A|`. -/
theorem natCard_ne_zero_brauer {A : Type*} [Group A] [Fintype A] {r : ℕ} [Fact r.Prime]
    (hcop : Nat.Coprime r (Nat.card A)) :
    (Nat.card A : Work.Hering.AppVII.BrauerField r) ≠ 0 := by
  intro h
  exact Work.Hering.AppVII.not_dvd_card hcop
    ((CharP.cast_eq_zero_iff (Work.Hering.AppVII.BrauerField r) r (Nat.card A)).mp h)

/-- `|C|` is non-zero in `k = F̄_r` when `r ∤ |A|` and `C ≤ A`. -/
theorem card_subgroup_ne_zero_brauer {A : Type*} [Group A] [Fintype A] {r : ℕ} [Fact r.Prime]
    (hcop : Nat.Coprime r (Nat.card A)) (C : Subgroup A) [Fintype ↥C] :
    (Nat.card ↥C : Work.Hering.AppVII.BrauerField r) ≠ 0 := by
  intro h
  exact Work.Hering.AppVII.not_dvd_card hcop
    (dvd_trans ((CharP.cast_eq_zero_iff (Work.Hering.AppVII.BrauerField r) r (Nat.card ↥C)).mp h)
      (Subgroup.card_subgroup_dvd_card C))

/-- **Step 1.**  If a `k[A]`-module `V` has `V^C = 0`, then the sum of the operators `ρ c`
over `c ∈ C` vanishes. -/
theorem sum_rho_eq_zero {A : Type*} [Group A] [Fintype A] {r : ℕ} [Fact r.Prime]
    {V : Type*} [AddCommGroup V] [Module (Work.Hering.AppVII.BrauerField r) V]
    (ρ : Representation (Work.Hering.AppVII.BrauerField r) A V) (C : Subgroup A) [Fintype ↥C]
    (hC : ∀ v : V, (∀ c ∈ C, ρ c v = v) → v = 0) :
    (∑ c : ↥C, ρ (c : A)) = 0 := by
  ext v
  rw [LinearMap.sum_apply, LinearMap.zero_apply]
  refine hC (∑ c : ↥C, ρ (c : A) v) (fun c hc => ?_)
  have hstep : ρ c (∑ d : ↥C, ρ (d : A) v) = ∑ d : ↥C, ρ (d : A) v := by
    rw [map_sum]
    rw [show (∑ d : ↥C, (ρ c) (ρ (d : A) v))
        = ∑ d : ↥C, ρ ((⟨c, hc⟩ * d : ↥C) : A) v from
      Finset.sum_congr rfl (fun d _ => by
        rw [← Module.End.mul_apply, ← map_mul]
        rfl)]
    exact Equiv.sum_comp (Equiv.mulLeft (⟨c, hc⟩ : ↥C)) (fun d : ↥C => ρ (d : A) v)
  exact hstep

/-- The coefficient of `Eℂ χ = irrDeg χ • ∑_g χ(g⁻¹) • single g 1`. -/
theorem Eℂ_coeff {A : Type*} [Group A] [Fintype A] (χ : A → ℂ) (g : A) :
    (Work.Hering.AppVII.Eℂ χ).coeff g = (Work.CharCore.irrDeg χ : ℂ) * χ g⁻¹ := by
  rw [Work.Hering.AppVII.Eℂ, MonoidAlgebra.coeff_smul_apply]
  congr 1
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single g]
  · simp
  · intro b _ hb; simp [Finsupp.single_eq_of_ne (Ne.symm hb)]
  · intro h; exact absurd (Finset.mem_univ g) h

/-- The coefficient of `single 1` in `(∑_{c ∈ C} single c 1) · Eℂ χ`. -/
theorem coeff_one_rhoC_mul_Eℂ {A : Type*} [Group A] [Fintype A]
    (C : Subgroup A) [Fintype ↥C] (χ : A → ℂ) :
    ((∑ c : ↥C, MonoidAlgebra.single (c : A) (1 : ℂ)) * Work.Hering.AppVII.Eℂ χ).coeff 1
      = (Work.CharCore.irrDeg χ : ℂ) * ∑ c : ↥C, χ (c : A) := by
  rw [Finset.sum_mul]
  rw [show (∑ c : ↥C, MonoidAlgebra.single (c : A) (1 : ℂ) * Work.Hering.AppVII.Eℂ χ).coeff
      = ∑ c : ↥C, (MonoidAlgebra.single (c : A) (1 : ℂ) * Work.Hering.AppVII.Eℂ χ).coeff from
    MonoidAlgebra.coeff_sum _ _]
  rw [show (∑ c : ↥C,
        (MonoidAlgebra.single (c : A) (1 : ℂ) * Work.Hering.AppVII.Eℂ χ).coeff) 1
      = ∑ c : ↥C,
        (MonoidAlgebra.single (c : A) (1 : ℂ) * Work.Hering.AppVII.Eℂ χ).coeff 1 from
    Finsupp.finsetSum_apply _ _ _]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [MonoidAlgebra.single_mul_apply, Eℂ_coeff, mul_one, inv_inv, one_mul]

/-- **The complex side of the coprime Brauer correspondence.**  If the `C`-averaged integral
lift of the idempotent `e_χ` vanishes, then `∑_{c ∈ C} χ c = 0`. -/
theorem CharSumZeroOfTildeE {A : Type*} [Group A] [Fintype A]
    (C : Subgroup A) [Fintype ↥C] (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A)
    (h : (∑ c : ↥C, MonoidAlgebra.single (c : A)
            (1 : Work.Hering.AppVII.CycloRing (Nat.card A))) *
          Work.Hering.AppVII.tildeE χ hχ = 0) :
    ∑ c : ↥C, χ (c : A) = 0 := by
  have hsum : MonoidAlgebra.mapRingHom A (Work.Hering.AppVII.iota (Nat.card A))
      (∑ c : ↥C, MonoidAlgebra.single (c : A)
        (1 : Work.Hering.AppVII.CycloRing (Nat.card A)))
      = ∑ c : ↥C, MonoidAlgebra.single (c : A) (1 : ℂ) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [MonoidAlgebra.mapRingHom_single, map_one]
  have hmap : MonoidAlgebra.mapRingHom A (Work.Hering.AppVII.iota (Nat.card A))
      ((∑ c : ↥C, MonoidAlgebra.single (c : A)
          (1 : Work.Hering.AppVII.CycloRing (Nat.card A))) *
        Work.Hering.AppVII.tildeE χ hχ) = (0 : MonoidAlgebra ℂ A) := by
    rw [h]
    exact map_zero _
  rw [map_mul, hsum, show MonoidAlgebra.mapRingHom A (Work.Hering.AppVII.iota (Nat.card A))
        (Work.Hering.AppVII.tildeE χ hχ) = Work.Hering.AppVII.Eℂ χ from
    MapIotaTildeE χ hχ] at hmap
  have h3 : ((∑ c : ↥C, MonoidAlgebra.single (c : A) (1 : ℂ)) *
      Work.Hering.AppVII.Eℂ χ).coeff 1 = 0 := by
    rw [hmap]
    simp
  rw [coeff_one_rhoC_mul_Eℂ C χ] at h3
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact absurd h4 (Work.CharCore.irrDeg_ne_zero hχ)
  · exact h4

/-- **Vanishing of the character sum on a fixed-point-free subgroup** (coprime Brauer case).

Let `A` be a finite group, `r ∤ |A|`, `k = F̄_r`, `V` an irreducible `k[A]`-module, `C ≤ A` a
subgroup such that `V^C = 0`, and `χ ∈ Irr_ℂ A` the ordinary irreducible character of the block
acting as the identity on `V` (hypothesis `hblock`).  Then `∑_{c ∈ C} χ(c) = 0`.

Route: the sum `ρ_C := ∑_{c ∈ C} ρ c` of the operators vanishes on `V` (its image consists of
`C`-fixed vectors, hence is `0`).  Since `e_χ = toK hcop χ hχ` is a primitive central
idempotent of `k[A]` which acts as the identity on `V`, the annihilator of `V` inside the block
`k[A]e_χ` is trivial, so `ρ_C · e_χ = 0`.  Lifting this identity along the reduction
`ℤ[ζ_|A|] → k` gives `(∑_{c ∈ C} single c 1)·tildeE χ hχ = 0` in `ℤ[ζ_|A|][A]`, and taking the
coefficient of `1` (equivalently, applying `iota`) gives `χ(1)·∑_{c ∈ C} χ(c) = 0`. -/
theorem BrauerSumZero {A : Type*} [Group A] [Fintype A] {r : ℕ} [Fact r.Prime]
    (hcop : Nat.Coprime r (Nat.card A))
    (hprops :
      (∀ (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A),
          Work.Hering.AppVII.IsCentralIdempotent (Work.Hering.AppVII.toK hcop χ hχ)) ∧
      (∀ (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A), Work.Hering.AppVII.toK hcop χ hχ ≠ 0) ∧
      (∀ (χ χ' : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A) (hχ' : χ' ∈ Work.CharCore.Irr A), χ ≠ χ' →
          Work.Hering.AppVII.toK hcop χ hχ * Work.Hering.AppVII.toK hcop χ' hχ' = 0) ∧
      (Finset.sum (Work.CharCore.Irr A).attach (fun x => Work.Hering.AppVII.toK hcop x.1 x.2) = 1) ∧
      (∀ (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A) (z : A), χ z = χ 1 →
          Work.Hering.AppVII.toK hcop χ hχ *
            MonoidAlgebra.single z (1 : Work.Hering.AppVII.BrauerField r) =
          Work.Hering.AppVII.toK hcop χ hχ))
    {V : Type*} [AddCommGroup V] [Module (Work.Hering.AppVII.BrauerField r) V]
    [Module.Finite (Work.Hering.AppVII.BrauerField r) V]
    (ρ : Representation (Work.Hering.AppVII.BrauerField r) A V) (hρ : ρ.IsIrreducible)
    (C : Subgroup A) [Fintype ↥C] (hC : ∀ v : V, (∀ c ∈ C, ρ c v = v) → v = 0)
    (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A)
    (hblock : ρ.asAlgebraHom (Work.Hering.AppVII.toK hcop χ hχ) = 1) :
    ∑ c : ↥C, χ (c : A) = 0 := by
  have hρC0 : ρ.asAlgebraHom
      (∑ c : ↥C, MonoidAlgebra.single (c : A)
        (1 : Work.Hering.AppVII.BrauerField r)) = 0 := by
    rw [map_sum]
    rw [show (∑ c : ↥C, ρ.asAlgebraHom (MonoidAlgebra.single (c : A)
          (1 : Work.Hering.AppVII.BrauerField r)))
        = ∑ c : ↥C, ρ (c : A) from
      Finset.sum_congr rfl (fun c _ => Representation.asAlgebraHom_single_one ρ (c : A))]
    exact sum_rho_eq_zero ρ C hC
  have h1 : (∑ c : ↥C, MonoidAlgebra.single (c : A)
        (1 : Work.Hering.AppVII.BrauerField r)) *
      Work.Hering.AppVII.toK hcop χ hχ = 0 :=
    BlockInjectivePrim hcop χ hχ (ToKPrimitive hcop hprops χ hχ) ρ hρ hblock
      ((∑ c : ↥C, MonoidAlgebra.single (c : A)
          (1 : Work.Hering.AppVII.BrauerField r)) * Work.Hering.AppVII.toK hcop χ hχ)
      (by rw [mul_assoc, (hprops.1 χ hχ).1])
      (by rw [map_mul, hρC0, hblock, mul_one])
  exact CharSumZeroOfTildeE C χ hχ (RhoCTildeE hcop χ hχ C h1)

end

end Work.NormalComplement.AppVII
