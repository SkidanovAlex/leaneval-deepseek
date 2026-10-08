import Mathlib
import Submission.Work.CORE3.Defs

namespace Work.CORE3

theorem NotLeCentralizerOfIsFourGroup {X : Type} [Group X] (V : Subgroup X) (s : X)
    (hV4 : Work.GW2.IsFourGroup V) (hs2 : orderOf s = 2) (hsV : s ∉ V)
    (hno : ¬ ∃ W : Subgroup X, Nat.card W = 8 ∧ ∀ x ∈ W, x ^ 2 = 1) :
    ¬ V ≤ Subgroup.centralizer ({s} : Set X) := by
  intro hC
  -- `s` is an involution.
  have hs2' : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs2] at h
    simpa [pow_two] using h
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2'
  -- every element of `V` commutes with `s`, hence `s` normalises `V` on each side.
  have hcomm : ∀ v ∈ V, s * v = v * s := by
    intro v hv
    exact (Subgroup.mem_centralizer_iff.mp (hC hv)) s (by simp)
  -- `⟨V, s⟩` is the set `V ∪ V·s`; it is a subgroup because `s` commutes with `V`.
  let S : Subgroup X :=
    { carrier := {x : X | ∃ v ∈ V, x = v ∨ x = v * s}
      mul_mem' := by
        rintro a b ⟨v1, hv1, ha | ha⟩ ⟨v2, hv2, hb | hb⟩
        · exact ⟨v1 * v2, V.mul_mem hv1 hv2, Or.inl (by rw [ha, hb])⟩
        · exact ⟨v1 * v2, V.mul_mem hv1 hv2, Or.inr (by rw [ha, hb, mul_assoc])⟩
        · refine ⟨v1 * v2, V.mul_mem hv1 hv2, Or.inr ?_⟩
          rw [ha, hb, mul_assoc, hcomm v2 hv2, ← mul_assoc]
        · refine ⟨v1 * v2, V.mul_mem hv1 hv2, Or.inl ?_⟩
          rw [ha, hb]
          calc v1 * s * (v2 * s) = v1 * (s * (v2 * s)) := by rw [mul_assoc]
            _ = v1 * ((s * v2) * s) := by rw [mul_assoc s v2 s]
            _ = v1 * ((v2 * s) * s) := by rw [hcomm v2 hv2]
            _ = v1 * (v2 * (s * s)) := by rw [mul_assoc v2 s s]
            _ = v1 * v2 := by rw [hs2', mul_one]
      one_mem' := ⟨1, V.one_mem, Or.inl rfl⟩
      inv_mem' := by
        rintro a ⟨v, hv, ha | ha⟩
        · exact ⟨v⁻¹, V.inv_mem hv, Or.inl (by rw [ha])⟩
        · refine ⟨v⁻¹, V.inv_mem hv, Or.inr ?_⟩
          rw [ha, mul_inv_rev, hsinv]
          exact hcomm v⁻¹ (V.inv_mem hv) }
  have hS : ∀ x, x ∈ S ↔ ∃ v ∈ V, x = v ∨ x = v * s := fun x => Iff.rfl
  -- `S` has exponent two.
  have hsq : ∀ x ∈ S, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨v, hv, hx | hx⟩ := (hS x).mp hx
    · rw [hx]; exact hV4.2 v hv
    · rw [hx, pow_two]
      calc v * s * (v * s) = v * (s * (v * s)) := by rw [mul_assoc]
        _ = v * ((s * v) * s) := by rw [mul_assoc s v s]
        _ = v * ((v * s) * s) := by rw [hcomm v hv]
        _ = v * (v * (s * s)) := by rw [mul_assoc v s s]
        _ = v * v := by rw [hs2', mul_one]
        _ = 1 := by simpa [pow_two] using hV4.2 v hv
  -- `S` is in bijection with `V × Bool`, hence `Nat.card S = 4 * 2 = 8`.
  have hcard : Nat.card S = 8 := by
    have hinj : Function.Injective (fun p : V × Bool =>
        (match p.2 with
         | false => (⟨p.1.1, by rw [hS]; exact ⟨p.1, p.1.2, Or.inl rfl⟩⟩ : S)
         | true  => (⟨p.1.1 * s, by rw [hS]; exact ⟨p.1, p.1.2, Or.inr rfl⟩⟩ : S))) := by
      rintro ⟨⟨v1, hv1⟩, b1⟩ ⟨⟨v2, hv2⟩, b2⟩ h
      cases b1 <;> cases b2
      · have hX : (v1 : X) = (v2 : X) := congrArg Subtype.val h
        exact Prod.ext (Subtype.ext hX) rfl
      · exfalso
        have hX : (v1 : X) = (v2 : X) * s := congrArg Subtype.val h
        apply hsV
        have : (v2 : X)⁻¹ * v1 = s := by rw [hX]; group
        rw [← this]
        exact V.mul_mem (V.inv_mem hv2) hv1
      · exfalso
        have hX : (v1 : X) * s = (v2 : X) := congrArg Subtype.val h
        apply hsV
        have : (v1 : X)⁻¹ * v2 = s := by rw [← hX]; group
        rw [← this]
        exact V.mul_mem (V.inv_mem hv1) hv2
      · have hX : (v1 : X) * s = (v2 : X) * s := congrArg Subtype.val h
        have hvv : (v1 : X) = (v2 : X) := mul_right_cancel hX
        exact Prod.ext (Subtype.ext hvv) rfl
    have hsurj : Function.Surjective (fun p : V × Bool =>
        (match p.2 with
         | false => (⟨p.1.1, by rw [hS]; exact ⟨p.1, p.1.2, Or.inl rfl⟩⟩ : S)
         | true  => (⟨p.1.1 * s, by rw [hS]; exact ⟨p.1, p.1.2, Or.inr rfl⟩⟩ : S))) := by
      intro x
      obtain ⟨v, hv, hx | hx⟩ := (hS x.1).mp x.2
      · exact ⟨(⟨v, hv⟩, false), Subtype.ext hx.symm⟩
      · exact ⟨(⟨v, hv⟩, true), Subtype.ext hx.symm⟩
    have hthis : Nat.card (V × Bool) = Nat.card S :=
      Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)
    have hprod : Nat.card (V × Bool) = 8 := by
      rw [Nat.card_prod, hV4.1, Nat.card_eq_fintype_card, Fintype.card_bool]
    rw [← hthis, hprod]
  exact hno ⟨S, hcard, hsq⟩

end Work.CORE3
