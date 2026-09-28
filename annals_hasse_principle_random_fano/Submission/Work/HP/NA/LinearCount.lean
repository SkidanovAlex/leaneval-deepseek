import Submission.Work.HP.NA.Setup

/-!
# Counting solutions of linear congruences over `ZMod q`

`card_ker_single`: the number of `a ∈ (ZMod q)^N` with `∑ aᵢ vᵢ = 0` is `q^(N-1)` when `v` is
primitive modulo `q` (some coordinate a unit).
-/

noncomputable section
open Finset
set_option autoImplicit false

namespace Work.HP
namespace NA

/-- Number of solutions of one linear congruence with a primitive coefficient vector. -/
theorem card_ker_single {q N : ℕ} (hq : 0 < q) (hN : 1 ≤ N) (v : Fin N → ZMod q)
    (i0 : Fin N) (hu : IsUnit (v i0)) :
    Nat.card {a : Fin N → ZMod q // ∑ i, a i * v i = 0} = q ^ (N - 1) := by
  let f : (Fin N → ZMod q) →ₗ[ZMod q] ZMod q :=
    { toFun := fun a => ∑ i, a i * v i
      map_add' := by
        intro a b
        rw [Finset.sum_congr rfl (fun i _ => by rw [Pi.add_apply, add_mul])]
        rw [Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring) }
  have hsurj : Function.Surjective f := by
    intro y
    refine ⟨fun i => if i = i0 then (↑hu.unit⁻¹) * y else 0, ?_⟩
    change (∑ i, (if i = i0 then (↑hu.unit⁻¹) * y else 0) * v i) = y
    rw [Finset.sum_eq_single_of_mem i0 (Finset.mem_univ i0)]
    · rw [if_pos rfl]
      calc (↑hu.unit⁻¹ * y) * v i0 = y * (↑hu.unit⁻¹ * v i0) := by ring
        _ = y := by rw [hu.val_inv_mul, mul_one]
    · intro b _ hb; rw [if_neg hb]; ring
  have hsub : Nat.card {a : Fin N → ZMod q // ∑ i, a i * v i = 0} = Nat.card ↥f.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun a => by rw [LinearMap.mem_ker]; exact Iff.rfl))
  rw [hsub]
  have hcard := Submodule.card_eq_card_quotient_mul_card f.ker
  have hdom : Nat.card (Fin N → ZMod q) = q ^ N := by
    rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod]
  have hrange : Nat.card ↥f.range = q := by
    have htop : f.range = ⊤ := LinearMap.range_eq_top.mpr hsurj
    rw [htop]
    exact (Nat.card_congr Submodule.topEquiv.toEquiv).trans (Nat.card_zmod q)
  have hquot : Nat.card ((Fin N → ZMod q) ⧸ f.ker) = q :=
    (Nat.card_congr (LinearMap.quotKerEquivRange f).toEquiv).trans hrange
  rw [hdom, hquot] at hcard
  refine Nat.eq_of_mul_eq_mul_right hq ?_
  have h2 : q ^ (N - 1) * q = q ^ N := by
    rw [← Nat.pow_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hN]
  rw [hcard.symm, h2]

end NA
end Work.HP
