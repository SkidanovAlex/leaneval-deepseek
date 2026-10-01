import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs

namespace Work.LinnikBurgess

/-- In `ZMod (p^K)` (with `p` prime) the annihilator of `δ` is the annihilator of the pure
`p`-power `p ^ vcap p K δ.val`: multiplying `h` by `δ` kills it exactly when multiplying `h`
by that power of `p` does.  Indeed, writing the representative `δ.val = p^v * u` with
`u` coprime to `p` (hence a unit of `ZMod (p^K)`, `v = padicValNat p δ.val`), the unit `u`
can be cancelled. -/
theorem vcap_kernel_eq {p K : ℕ} [Fact p.Prime] (hK : 1 ≤ K) (δ h : ZMod (p ^ K)) :
    (δ * h = 0) ↔ (((p ^ vcap p K δ.val : ℕ) : ZMod (p ^ K)) * h = 0) := by
  haveI : NeZero (p ^ K) := ⟨pow_ne_zero K (Fact.out : p.Prime).ne_zero⟩
  rcases eq_or_ne δ.val 0 with hx | hx
  · -- `δ = 0`, and `p ^ vcap p K 0 = p ^ K = 0` in `ZMod (p^K)`.
    have hδ0 : δ = 0 := (ZMod.val_eq_zero δ).mp hx
    have hvK : vcap p K δ.val = K := by rw [vcap, if_pos hx]
    rw [hvK, hδ0, ZMod.natCast_self, zero_mul]
  · -- `δ.val ≠ 0`: `v = padicValNat p δ.val < K`, and `δ` is a unit times `p^v`.
    obtain ⟨v, hv⟩ : ∃ v : ℕ, v = padicValNat p δ.val := ⟨_, rfl⟩
    have hdvd : p ^ v ∣ δ.val := by rw [hv]; exact pow_padicValNat_dvd
    have hlt : v < K := by
      have hnot : ¬ (p ^ K ∣ δ.val) := by
        intro hd
        have hpos : 0 < δ.val := Nat.pos_of_ne_zero hx
        have hle : p ^ K ≤ δ.val := Nat.le_of_dvd hpos hd
        have := ZMod.val_lt δ
        omega
      by_contra hcon
      rw [hv, not_lt] at hcon
      exact hnot ((padicValNat_dvd_iff_le (p := p) (n := K) (a := δ.val) hx).mpr hcon)
    have hvcap : vcap p K δ.val = v := by
      rw [vcap, if_neg hx, ← hv]
      exact min_eq_left (le_of_lt hlt)
    obtain ⟨u, hu⟩ : ∃ u : ℕ, u = δ.val / p ^ v := ⟨_, rfl⟩
    have hmul : p ^ v * u = δ.val := by rw [hu]; exact Nat.mul_div_cancel' hdvd
    have hu0 : u ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hmul
      exact hx hmul.symm
    have hpadu : padicValNat p u = 0 := by
      have hh := padicValNat.div_pow (p := p) (b := δ.val) (a := v) hdvd
      rw [← hu, hv, Nat.sub_self] at hh
      exact hh
    have hpnu : ¬ p ∣ u := by
      rcases (padicValNat.eq_zero_iff (p := p) (n := u)).mp hpadu with h' | h' | h'
      · exact absurd h' (Fact.out : p.Prime).ne_one
      · exact absurd h' hu0
      · exact h'
    have hcop : Nat.Coprime u (p ^ K) :=
      (((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpnu).symm).pow_right K
    obtain ⟨U, hU⟩ : ∃ U : (ZMod (p ^ K))ˣ, (U : ZMod (p ^ K)) = (u : ZMod (p ^ K)) :=
      ⟨ZMod.unitOfCoprime u hcop, ZMod.coe_unitOfCoprime u hcop⟩
    have hdecomp : δ = ((p ^ v : ℕ) : ZMod (p ^ K)) * (U : ZMod (p ^ K)) := by
      calc δ = ((δ.val : ℕ) : ZMod (p ^ K)) := (ZMod.natCast_zmod_val δ).symm
        _ = ((p ^ v * u : ℕ) : ZMod (p ^ K)) := by rw [hmul]
        _ = ((p ^ v : ℕ) : ZMod (p ^ K)) * (u : ZMod (p ^ K)) := by push_cast; ring
        _ = ((p ^ v : ℕ) : ZMod (p ^ K)) * (U : ZMod (p ^ K)) := by rw [hU]
    rw [hvcap, hdecomp]
    have hkey : (((p ^ v : ℕ) : ZMod (p ^ K)) * (U : ZMod (p ^ K))) * h
        = (U : ZMod (p ^ K)) * (((p ^ v : ℕ) : ZMod (p ^ K)) * h) := by ring
    rw [hkey]
    exact IsUnit.mul_right_eq_zero (Units.isUnit U)

end Work.LinnikBurgess
