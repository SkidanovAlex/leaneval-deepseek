import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.FieldTheory.PrimitiveRoot

theorem exists_isPrimitiveRoot_of_dvd_card_sub_one {F : Type*} [Field F] [Fintype F] {e : ℕ}
    (he : 1 ≤ e) (hdiv : e ∣ Fintype.card F - 1) : ∃ ζ : F, IsPrimitiveRoot ζ e := by
  classical
  have hdiv' : e ∣ Fintype.card Fˣ := by
    rw [Fintype.card_units]; exact hdiv
  have hcard : (Finset.univ.filter (fun a : Fˣ => orderOf a = e)).card = Nat.totient e :=
    IsCyclic.card_orderOf_eq_totient hdiv'
  have hpos : 0 < Nat.totient e := Nat.totient_pos.mpr (by omega)
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by rw [hcard]; exact hpos)
  rw [Finset.mem_filter] at ha
  obtain ⟨-, hae⟩ := ha
  refine ⟨(a : F), ?_⟩
  refine ⟨?_, ?_⟩
  · have h : a ^ e = 1 := by rw [← hae, pow_orderOf_eq_one]
    have := congrArg (fun u : Fˣ => (u : F)) h
    simpa using this
  · intro l hl
    have h : a ^ l = 1 := Units.ext (by simpa using hl)
    have h2 : orderOf a ∣ l := orderOf_dvd_iff_pow_eq_one.mpr h
    rwa [hae] at h2

end Commons.FieldTheory.PrimitiveRoot