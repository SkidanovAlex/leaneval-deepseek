import Mathlib
import Submission.Work.TMC16Core.Basic.nnDist
import Submission.Work.Core.exists_nn_le

/-!
# Separation of the `nn`-grid `2x + k·p/q`, `k ∈ {1,…,q}`

Let `q > 0`, let `p : ℤ` be coprime to `q` and let `x : ℝ`.  Consider the `q` real numbers

  `w k = nn (2x + k·(p/q))`,   `k ∈ {1,…,q}`,

where `nn` is the distance to the nearest integer (`Work.TMC16Core.Basic.nn`).  If `k₁`
realises the minimum of `k ↦ w k` over `{1,…,q}`, then

* every *other* value `w k`, `k ≠ k₁`, is at least `1/(2q)`, and
* the minimum `w k₁` is at most `1/(2q)`.

**Mathematics.**  Since `gcd (p.natAbs) q = 1`, the values `k·p/q` for `k ∈ {1,…,q}` run
over all residues `j/q`, `j ∈ {0,…,q-1}` exactly once; consequently the `q` points
`2x + k·p/q` are equally spaced by `1/q` on the circle, so the closest one to an integer
is at distance `≤ 1/(2q)` while the difference of any two distinct ones is a non-integer
rational with denominator `q`, hence at distance `≥ 1/q` from every integer.  Both facts
are formalised below:

* `Work.Core.exists_nn_le` provides the `≤ 1/(2q)` bound for *some* `k`, and `hmin`
  transfers it to `k₁`;
* for `k ≠ k₁` one writes `A - B = ((k-k₁)·p)/q` with `B` the value at `k₁`, and uses
  `nn (N/q) ≥ 1/q` for an integer `N` not divisible by `q` (see `nn_int_div_nat_ge`),
  together with `nn (A-B) ≤ nn A + nn B` and `nn B ≤ nn A`.
-/

namespace Work.TMC16Core.Trig

open Work.TMC16Core.Basic

/-- `nn` is even (the distance to the nearest integer does not see the sign). -/
private lemma nn_neg' (w : ℝ) : nn (-w) = nn w := by
  apply le_antisymm
  · simp only [nn]
    calc |-w - ↑(round (-w))| ≤ |-w + ↑(round w)| := by
            simpa using round_le (-w) (-(round w))
      _ = |w - ↑(round w)| := by
            rw [show (-w : ℝ) + ↑(round w) = -(w - ↑(round w)) by ring, abs_neg]
  · simp only [nn]
    calc |w - ↑(round w)| ≤ |w + ↑(round (-w))| := by
            simpa using round_le w (-(round (-w)))
      _ = |-w - ↑(round (-w))| := by
            rw [show (w : ℝ) + ↑(round (-w)) = -(-w - ↑(round (-w))) by ring, abs_neg]

/-- Triangle inequality for `nn` in the form `nn (a-b) ≤ nn a + nn b`. -/
private lemma nn_sub_le' (a b : ℝ) : nn (a - b) ≤ nn a + nn b := by
  have h : a - b = a + (-b) := by ring
  rw [h]
  calc nn (a + -b) ≤ nn a + nn (-b) := nn_add_le a (-b)
    _ = nn a + nn b := by rw [nn_neg']

/-- The absolute value of the real image of an integer is its `natAbs`. -/
private lemma nn_abs_intCast (z : ℤ) : |((z:ℤ):ℝ)| = ((z.natAbs : ℕ) : ℝ) := by
  rw [← Int.cast_abs, Int.abs_eq_natAbs]; simp

/-- **Key lower bound.**  If the integer `N` is not divisible by `q > 0`, then
`N/q` is at distance at least `1/q` from every integer. -/
private lemma nn_int_div_nat_ge (N : ℤ) {q : ℕ} (hq : 0 < q) (hndvd : ¬ (q:ℤ) ∣ N) :
    1/(q:ℝ) ≤ nn ((N:ℝ)/(q:ℝ)) := by
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  rw [nn]
  set m : ℤ := round ((N:ℝ)/(q:ℝ)) with hm
  have hz : N - m * (q:ℤ) ≠ 0 := by
    intro h
    apply hndvd
    exact ⟨m, by linarith⟩
  have hdiff : (N:ℝ)/(q:ℝ) - (m:ℝ) = (((N - m*(q:ℤ)):ℤ):ℝ) / (q:ℝ) := by
    push_cast; field_simp
  rw [hdiff, abs_div, abs_of_pos hqR, nn_abs_intCast]
  have hge : (1:ℝ) ≤ ((N - m*(q:ℤ)).natAbs : ℝ) := by
    have : 1 ≤ (N - m*(q:ℤ)).natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hz)
    exact_mod_cast this
  exact div_le_div_of_nonneg_right hge hqR.le

/-- Euclid's lemma over `ℤ`, coprime form: if `p` is coprime to `q` and `q ∣ d * p`,
then `q ∣ d`. -/
private lemma dvd_of_dvd_mul_of_coprime {p d : ℤ} {q : ℕ} (hcop : Nat.Coprime p.natAbs q)
    (h : (q:ℤ) ∣ d * p) : (q:ℤ) ∣ d := by
  have hgcd : Int.gcd p (q:ℤ) = 1 := by
    rw [Int.gcd_eq_natAbs, Int.natAbs_natCast]
    exact hcop.gcd_eq_one
  have hbez : p * p.gcdA (q:ℤ) + (q:ℤ) * p.gcdB (q:ℤ) = 1 := by
    have hh := Int.gcd_eq_gcd_ab p (q:ℤ)
    rw [hgcd] at hh
    norm_num at hh
    exact hh.symm
  have hd : d = (d * p) * p.gcdA (q:ℤ) + (d * p.gcdB (q:ℤ)) * (q:ℤ) := by
    calc d = d * (p * p.gcdA (q:ℤ) + (q:ℤ) * p.gcdB (q:ℤ)) := by rw [hbez, mul_one]
      _ = (d * p) * p.gcdA (q:ℤ) + (d * p.gcdB (q:ℤ)) * (q:ℤ) := by ring
  rw [hd]
  exact dvd_add (h.mul_right _) (dvd_mul_left (q:ℤ) (d * p.gcdB (q:ℤ)))

/-- With `p` coprime to `q` and `0 < |d| < q`, the product `d * p` is not divisible
by `q`. -/
private lemma not_dvd_mul {p : ℤ} {q : ℕ} (hcop : Nat.Coprime p.natAbs q)
    {d : ℤ} (hd0 : d ≠ 0) (hdl : d.natAbs < q) : ¬ (q:ℤ) ∣ d * p := by
  intro h
  have hdvd : (q:ℤ) ∣ d := dvd_of_dvd_mul_of_coprime hcop h
  obtain ⟨t, ht⟩ := hdvd
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
    exact hd0 ht
  have hnat : d.natAbs = q * t.natAbs := by
    rw [ht, Int.natAbs_mul, Int.natAbs_natCast]
  have h1 : 1 ≤ t.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr ht0)
  have hqle : q ≤ d.natAbs := by
    rw [hnat]
    calc q = q * 1 := by ring
      _ ≤ q * t.natAbs := Nat.mul_le_mul_left q h1
  omega

theorem grid_sep {q : ℕ} (hq : 0 < q) {p : ℤ} (hcop : Nat.Coprime p.natAbs q) (x : ℝ)
    {k₁ : ℕ} (hk₁ : k₁ ∈ Finset.Icc 1 q)
    (hmin : ∀ k ∈ Finset.Icc 1 q,
      Work.TMC16Core.Basic.nn (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))) ≥
        Work.TMC16Core.Basic.nn (2 * x + (k₁ : ℝ) * ((p : ℝ) / (q : ℝ)))) :
    (∀ k ∈ Finset.Icc 1 q, k ≠ k₁ →
      1 / (2 * (q : ℝ)) ≤
        Work.TMC16Core.Basic.nn (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ)))) ∧
    Work.TMC16Core.Basic.nn (2 * x + (k₁ : ℝ) * ((p : ℝ) / (q : ℝ))) ≤ 1 / (2 * (q : ℝ)) := by
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  refine ⟨?_, ?_⟩
  · -- the `≥ 1/(2q)` estimate for the non-minimal points
    intro k hk hne
    have hk1lo : 1 ≤ k₁ := (Finset.mem_Icc.mp hk₁).1
    have hk1hi : k₁ ≤ q := (Finset.mem_Icc.mp hk₁).2
    have hd0 : ((k:ℤ) - (k₁:ℤ)) ≠ 0 := by
      intro h
      apply hne
      have : (k:ℤ) = (k₁:ℤ) := by linarith
      exact_mod_cast this
    have hdl : ((k:ℤ) - (k₁:ℤ)).natAbs < q := by
      have hklo : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hkhi : k ≤ q := (Finset.mem_Icc.mp hk).2
      omega
    have hndvd : ¬ (q:ℤ) ∣ ((k:ℤ) - (k₁:ℤ)) * p := not_dvd_mul hcop hd0 hdl
    set D : ℝ := ((((k:ℤ)-(k₁:ℤ))*p : ℤ) : ℝ) / (q:ℝ) with hD
    have hlower : 1/(q:ℝ) ≤ nn D :=
      nn_int_div_nat_ge (((k:ℤ)-(k₁:ℤ))*p) hq hndvd
    have hdiff : (2*x + (k:ℝ)*((p:ℝ)/(q:ℝ))) - (2*x + (k₁:ℝ)*((p:ℝ)/(q:ℝ))) = D := by
      rw [hD]; push_cast; field_simp; ring
    have htri : nn D ≤ nn (2*x + (k:ℝ)*((p:ℝ)/(q:ℝ)))
        + nn (2*x + (k₁:ℝ)*((p:ℝ)/(q:ℝ))) := by
      rw [← hdiff]; exact nn_sub_le' _ _
    have hmink := hmin k hk
    have hkey : (1:ℝ)/(q:ℝ) ≤ 2 * nn (2*x + (k:ℝ)*((p:ℝ)/(q:ℝ))) := by linarith
    have hkey' : (1:ℝ) ≤ 2 * nn (2*x + (k:ℝ)*((p:ℝ)/(q:ℝ))) * (q:ℝ) :=
      (div_le_iff₀ hqR).mp hkey
    have h2q : (0:ℝ) < 2*(q:ℝ) := by linarith
    rw [div_le_iff₀ h2q]
    nlinarith [hkey']
  · -- the minimising point is within `1/(2q)` of an integer
    obtain ⟨k, hk, hle⟩ := Work.Core.exists_nn_le p q hq hcop (2*x)
    exact le_trans (hmin k hk) hle

end Work.TMC16Core.Trig
