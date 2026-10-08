import Mathlib
import Submission.Work.Hering.AppVII.brauer_lift_aux
import Submission.Work.Hering.AppVII.brauer_setup
import Submission.Work.CharCore.Main
import Submission.Work.NormalComplement.AppVII.TildeEProps
import Submission.Work.NormalComplement.AppVII.ToKProps
import Submission.Work.NormalComplement.AppVII.RhoCTildeEAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement.AppVII

open scoped BigOperators MonoidAlgebra

/-! ## The proof

(The docstring below is the original request; the proof supplied here follows a slightly
different route, summarised here.)

Write `R = ℤ[ζ_|A|]`, `k = F̄_r`, `ρ_C = ∑_{c ∈ C} single c 1`, `c = tildeE χ hχ` and
`f = ρ_C · c`.  Two integral elements of `R[A]` are annihilated on the right by `f`:

* `x = |C| • 1 - ρ_C`, since `f * ρ_C = ρ_C * c * ρ_C = ρ_C * ρ_C * c = |C| • f` uses the
  centrality of `c` and `ρ_C * ρ_C = |C| • ρ_C` (`sum_single_mul_sum_single`);
* `y = |A| • 1 - c`, since `f * c = ρ_C * (c * c) = |A| • f` uses `c * c = |A| • c`.

Hence `f * z = 0` for `z = x * c + |C| • y`.  Applying `psi hcop = MonoidAlgebra.mapRingHom A
(jred r |A| _)` to `z` gives, in `k[A]`,

`psi z = (|C|(1 - π))·(|A| e_χ) + |C|·(|A|(1 - e_χ)) = |A||C| • (e_χ + (1 - e_χ)) = |A||C| • 1`

where `π = |C|⁻¹ρ_C` and `e_χ = toK hcop χ hχ`, using `ρ_C · e_χ = 0` (the hypothesis) and
`psi (tildeE χ hχ) = |A| • e_χ`.  Since `|A|·|C|` is invertible in `k` (both factors are coprime
to `r`), the "regular representation" lemma
`eq_zero_of_mul_eq_zero_of_mapRingHom_eq_single_one` — `z` reduces to a non-zero scalar, so right
multiplication by `z` is injective — gives `f = 0`, as required. -/

/-- **Integral lifting of the `C`-averaged idempotent** (the Brauer lifting step).

Let `A` be finite, `r ∤ |A|`, `n = |A|`, `R = ℤ[ζ_n] = CycloRing n`, `k = F̄_r`, and let
`tildeE χ hχ ∈ R[A]` be the integral lift of `n·e_χ`, so that
`MonoidAlgebra.map (jred r n _) (tildeE χ hχ) = n • toK hcop χ hχ` in `k[A]`.

For a subgroup `C ≤ A` put `ρ_C = ∑_{c ∈ C} single c 1`.  If `ρ_C · toK hcop χ hχ = 0`
in `k[A]`, then `ρ_C · tildeE χ hχ = 0` in `R[A]`.

This is the lifting of a modular statement to characteristic zero; it is *not* formal: the
reduction `k[A]` of `R[A]` is not injective, and the hypothesis only says
`ρ_C·tildeE χ hχ ∈ 𝔪·R[A]` where `𝔪 = ker (jred r n _)`.

Suggested route: work over `R₂ = R[1/|C|]` (e.g. `Localization.Away (Nat.card ↥C)`), where the
`C`-averaging projector `π_C = |C|⁻¹·ρ_C ∈ R₂[A]` is defined.  Let `U₂ = R₂[A]·tildeE χ hχ`
and `D₂ = π_C(U₂)` (the `C`-fixed part of `U₂`); `D₂` is a finitely generated torsion-free
`R₂`-module.  Base change along `R₂ → k` (which exists since `r ∤ |C|`) gives
`D₂ ⊗_{R₂} k = π_C(U₂ ⊗ k) = π_C(k[A]·e_χ) = (k[A]e_χ)^C = 0`, because `ρ_C·e_χ = 0` and
`ρ_C` is central in `k[A]` (so `π_C(k[A]e_χ) = k[A]·π_C(e_χ) = 0`).  Hence `D₂ = 𝔪D₂`, and the
determinant trick (`Submodule.exists_sub_one_mem_and_smul_eq_of_fg_of_le_smul`) yields
`a ∈ 1 + 𝔪` with `a·D₂ = 0`; `a ≠ 0` and `D₂` torsion-free force `D₂ = 0`, so
`π_C(tildeE χ hχ) = 0`, i.e. `ρ_C·tildeE χ hχ = 0`.  (Equivalently, since
`MonoidAlgebra.map (iota n)` is injective, it suffices to prove `ρ_C · Eℂ χ = 0` in `ℂ[A]`,
where `Eℂ χ = MonoidAlgebra.map (iota n) (tildeE χ hχ)` by `MapIotaTildeE`.) -/
theorem RhoCTildeE {A : Type*} [Group A] [Fintype A] {r : ℕ} [Fact r.Prime]
    (hcop : Nat.Coprime r (Nat.card A)) (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A)
    (C : Subgroup A) [Fintype ↥C]
    (h : (∑ c : ↥C, MonoidAlgebra.single (c : A)
            (1 : Work.Hering.AppVII.BrauerField r)) *
          Work.Hering.AppVII.toK hcop χ hχ = 0) :
    (∑ c : ↥C, MonoidAlgebra.single (c : A)
        (1 : Work.Hering.AppVII.CycloRing (Nat.card A))) *
      Work.Hering.AppVII.tildeE χ hχ = 0 := by
  classical
  -- the two coefficient rings
  set R := Work.Hering.AppVII.CycloRing (Nat.card A)
  set k := Work.Hering.AppVII.BrauerField r
  -- the elements
  set ρR : MonoidAlgebra R A := ∑ c : ↥C, MonoidAlgebra.single (c : A) (1 : R) with hρR
  set ρk : MonoidAlgebra k A := ∑ c : ↥C, MonoidAlgebra.single (c : A) (1 : k) with hρk
  set c0 : MonoidAlgebra R A := Work.Hering.AppVII.tildeE χ hχ with hc0
  set f : MonoidAlgebra R A := ρR * c0 with hf
  set x : MonoidAlgebra R A := (Nat.card ↥C : R) • (1 : MonoidAlgebra R A) - ρR with hx
  set y : MonoidAlgebra R A := (Nat.card A : R) • (1 : MonoidAlgebra R A) - c0 with hy
  set z : MonoidAlgebra R A := x * c0 + (Nat.card ↥C : R) • y with hz
  -- ## The basic relations
  have hcsq : c0 * c0 = (Nat.card A : R) • c0 := by
    rw [hc0]; exact (TildeEProps (A := A)).2.1 χ hχ
  have hcc : ∀ w : MonoidAlgebra R A, w * c0 = c0 * w := by
    intro w; rw [hc0]; exact (TildeEProps (A := A)).1 χ hχ w
  have hρsq : ρR * ρR = (Nat.card ↥C : R) • ρR := by
    rw [hρR]; exact sum_single_mul_sum_single C
  -- ## `f` annihilates `x`, `y` and hence `z`
  have hfx : f * x = 0 := by
    rw [hf, hx, mul_sub, mul_smul_comm, mul_one, mul_assoc, ← hcc ρR, ← mul_assoc, hρsq,
      smul_mul_assoc, sub_self]
  have hfy : f * y = 0 := by
    rw [hf, hy, mul_sub, mul_smul_comm, mul_one, mul_assoc, hcsq, mul_smul_comm, sub_self]
  have hfz : f * z = 0 := by
    have h1 : f * (x * c0) = 0 := by rw [← mul_assoc, hfx, zero_mul]
    have h2 : f * ((Nat.card ↥C : R) • y) = 0 := by rw [mul_smul_comm, hfy, smul_zero]
    rw [hz, mul_add, h1, h2, add_zero]
  -- ## The image of `z` in `k[A]`
  have hpsiρ : psi hcop ρR = ρk := by
    rw [hρR, hρk, map_sum]
    exact Finset.sum_congr rfl fun c _ => psi_single_one hcop (c : A)
  have hn0 : (Nat.card A : k) ≠ 0 := natCast_ne_zero_brauer (Work.Hering.AppVII.not_dvd_card hcop)
  have hpsic : psi hcop c0 = (Nat.card A : k) • Work.Hering.AppVII.toK hcop χ hχ := by
    rw [hc0, Work.NormalComplement.AppVII.toK_eq_psi, smul_smul, mul_inv_cancel₀ hn0, one_smul]
  have hpsi_smul_one : ∀ m : ℕ, psi hcop ((m : R) • (1 : MonoidAlgebra R A)) =
      (m : k) • (1 : MonoidAlgebra k A) := by
    intro m
    rw [psi_smul, map_natCast, map_one]
  have hpsix : psi hcop x = (Nat.card ↥C : k) • (1 : MonoidAlgebra k A) - ρk := by
    rw [hx, map_sub, hpsi_smul_one, hpsiρ]
  have hpsiy : psi hcop y = (Nat.card A : k) • (1 : MonoidAlgebra k A) -
      (Nat.card A : k) • Work.Hering.AppVII.toK hcop χ hχ := by
    rw [hy, map_sub, hpsi_smul_one, hpsic]
  have hk : ρk * Work.Hering.AppVII.toK hcop χ hχ = 0 := by rw [hρk]; exact h
  have hpsiz : psi hcop z = MonoidAlgebra.single (1 : A)
      (Work.Hering.AppVII.jred r (Nat.card A) (Work.Hering.AppVII.not_dvd_card hcop)
        ((Nat.card A * Nat.card ↥C : ℕ) : R)) := by
    have h1 : psi hcop z = ((Nat.card ↥C : k) • (1 : MonoidAlgebra k A) - ρk) *
        ((Nat.card A : k) • Work.Hering.AppVII.toK hcop χ hχ) +
        (Nat.card ↥C : k) • ((Nat.card A : k) • (1 : MonoidAlgebra k A) -
          (Nat.card A : k) • Work.Hering.AppVII.toK hcop χ hχ) := by
      rw [hz, map_add, map_mul, psi_smul, map_natCast, hpsix, hpsic, hpsiy]
    have e1 : ((Nat.card ↥C : k) • (1 : MonoidAlgebra k A) - ρk) *
        ((Nat.card A : k) • Work.Hering.AppVII.toK hcop χ hχ) =
        ((Nat.card A : k) * (Nat.card ↥C : k)) • Work.Hering.AppVII.toK hcop χ hχ := by
      rw [sub_mul, smul_mul_assoc, one_mul, smul_smul, mul_smul_comm, hk, smul_zero, sub_zero,
        mul_comm (Nat.card ↥C : k) (Nat.card A : k)]
    have e2 : (Nat.card ↥C : k) • ((Nat.card A : k) • (1 : MonoidAlgebra k A) -
        (Nat.card A : k) • Work.Hering.AppVII.toK hcop χ hχ) =
        ((Nat.card A : k) * (Nat.card ↥C : k)) • (1 : MonoidAlgebra k A) -
        ((Nat.card A : k) * (Nat.card ↥C : k)) • Work.Hering.AppVII.toK hcop χ hχ := by
      rw [smul_sub, smul_smul, smul_smul, mul_comm (Nat.card ↥C : k) (Nat.card A : k)]
    have h2 : ((Nat.card ↥C : k) • (1 : MonoidAlgebra k A) - ρk) *
        ((Nat.card A : k) • Work.Hering.AppVII.toK hcop χ hχ) +
        (Nat.card ↥C : k) • ((Nat.card A : k) • (1 : MonoidAlgebra k A) -
          (Nat.card A : k) • Work.Hering.AppVII.toK hcop χ hχ) =
        ((Nat.card A : k) * (Nat.card ↥C : k)) • (1 : MonoidAlgebra k A) := by
      rw [e1, e2]
      abel
    have h3 : MonoidAlgebra.single (1 : A)
        (Work.Hering.AppVII.jred r (Nat.card A) (Work.Hering.AppVII.not_dvd_card hcop)
          ((Nat.card A * Nat.card ↥C : ℕ) : R)) =
        ((Nat.card A : k) * (Nat.card ↥C : k)) • (1 : MonoidAlgebra k A) := by
      rw [single_one_eq_smul_one, map_natCast, Nat.cast_mul]
    rw [h1, h2, h3]
  -- ## Apply the regular-representation lemma
  have hnC : ¬ r ∣ Nat.card A * Nat.card ↥C := by
    intro hd
    rcases (Fact.out : r.Prime).dvd_mul.mp hd with h1 | h2
    · exact Work.Hering.AppVII.not_dvd_card hcop h1
    · exact Work.Hering.AppVII.not_dvd_card hcop (dvd_trans h2 (Subgroup.card_subgroup_dvd_card C))
  refine eq_zero_of_mul_eq_zero_of_mapRingHom_eq_single_one
    (Work.Hering.AppVII.jred r (Nat.card A) (Work.Hering.AppVII.not_dvd_card hcop))
    ((Nat.card A * Nat.card ↥C : ℕ) : R) ?_ z f hpsiz hfz
  rw [map_natCast]
  exact natCast_ne_zero_brauer hnC

end Work.NormalComplement.AppVII
