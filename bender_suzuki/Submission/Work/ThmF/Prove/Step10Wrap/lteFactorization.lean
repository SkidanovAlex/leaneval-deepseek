import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.ThmF.Prove.Step10Wrap

/-- LTE (lifting the exponent) in the special case needed here: if `p` is an odd prime and
`f + 1 = p ^ m` with `m ≥ 1`, then the `p`-adic valuation of `f ^ p + 1` is `m + 1`.

This follows from Mathlib's `padicValNat.pow_add_pow`: applied with `x = f` and `y = 1` and
`n = p`, it gives `padicValNat p (f ^ p + 1) = padicValNat p (f + 1) + padicValNat p p`, and
`padicValNat p (f + 1) = padicValNat p (p ^ m) = m`, `padicValNat p p = 1`. -/
theorem lteFactorization {p m f : ℕ} (hp : p.Prime) (hodd : Odd p) (hm : 1 ≤ m) (hf : f + 1 = p ^ m) : (f ^ p + 1).factorization p = m + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- `p ∣ f + 1` since `f + 1 = p ^ m` with `m ≥ 1`.
  have hxy : p ∣ f + 1 := by rw [hf]; exact dvd_pow_self p (by omega)
  -- `p ∤ f`, because `p ∣ f` and `p ∣ f + 1` would force `p ∣ 1`.
  have hpf : ¬ p ∣ f := by
    intro h
    have h2 : p ∣ 1 := by
      have hs : p ∣ f + 1 - f := Nat.dvd_sub hxy h
      rwa [Nat.add_sub_cancel_left] at hs
    exact hp.not_dvd_one h2
  -- Convert the factorization into a `padicValNat`.
  rw [Nat.factorization_def (f ^ p + 1) hp]
  -- Lifting the exponent: `padicValNat p (f ^ p + 1) = padicValNat p (f + 1) + padicValNat p p`.
  have key : padicValNat p (f ^ p + 1) = padicValNat p (f + 1) + padicValNat p p := by
    simpa using padicValNat.pow_add_pow (p := p) (x := f) (y := 1) (n := p) hodd hxy hpf hodd
  rw [key, hf, padicValNat.prime_pow, padicValNat_self]

end Work.ThmF.Prove.Step10Wrap
