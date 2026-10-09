import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.TameData.Arithmetic

/-- **A prime is determined by any positive power of it**: if `p ^ f = p' ^ f'` with `p`, `p'`
prime and `f, f' > 0` then `p = p'` (`p` divides `p' ^ f'`, hence `p = p'`).  This is the step
which recovers the residue characteristic from the residue field order `q = p ^ f`. -/
theorem eq_of_prime_pow_eq_prime_pow {p p' f f' : ℕ} (hp : p.Prime) (hp' : p'.Prime)
    (hf : 0 < f) (hf' : 0 < f') (h : p ^ f = p' ^ f') : p = p' := by
  have h1 : p ∣ p' ^ f' := by rw [← h]; exact dvd_pow_self p hf.ne'
  have h2 : p' ∣ p ^ f := by rw [h]; exact dvd_pow_self p' hf'.ne'
  have h3 : p ∣ p' := hp.dvd_of_dvd_pow h1
  have h4 : p' ∣ p := hp'.dvd_of_dvd_pow h2
  exact le_antisymm (Nat.le_of_dvd hp'.pos h3) (Nat.le_of_dvd hp.pos h4)

end NK.TameData.Arithmetic
