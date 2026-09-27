import Mathlib
import Submission.Work.EQ.DefsCore

namespace Work.EQ

open Filter _root_.Topology

/-- If a function continuous at `0` vanishes on a punctured neighbourhood of `0`, then it vanishes
on a full neighbourhood of `0`. -/
lemma eventually_eq_zero_of_nhdsWithin_ne {f : ℂ → ℂ} (hf : ContinuousAt f (0 : ℂ))
    (h : ∀ᶠ u in 𝓝[≠] (0 : ℂ), f u = 0) : ∀ᶠ u in 𝓝 (0 : ℂ), f u = 0 := by
  have h' : f =ᶠ[𝓝[≠] (0 : ℂ)] (fun _ => (0 : ℂ)) := h
  have h0 : f 0 = 0 := by
    have ht1 : Tendsto f (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) :=
      tendsto_const_nhds.congr' h'.symm
    have ht2 : Tendsto f (𝓝[≠] (0 : ℂ)) (𝓝 (f 0)) :=
      continuousAt_iff_punctured_nhds.mp hf
    exact (tendsto_nhds_unique ht1 ht2).symm
  have hmem : insert (0 : ℂ) {u : ℂ | f u = 0} ∈ 𝓝 (0 : ℂ) :=
    insert_mem_nhds_iff.mpr h
  rwa [Set.insert_eq_of_mem (a := (0 : ℂ)) (s := {u : ℂ | f u = 0})
        (by simpa using h0)] at hmem

/-- If a function continuous at `0` vanishes on a punctured neighbourhood of `0`, then its value at
`0` is `0`. -/
lemma eq_zero_of_nhdsWithin_ne {f : ℂ → ℂ} (hf : ContinuousAt f (0 : ℂ))
    (h : ∀ᶠ u in 𝓝[≠] (0 : ℂ), f u = 0) : f 0 = 0 :=
  (eventually_eq_zero_of_nhdsWithin_ne hf h).self_of_nhds

/-- Composing a nonzero polynomial with the invertible linear substitution `X ↦ c⁻¹ X` gives a
nonzero polynomial. -/
private lemma comp_C_mul_X_ne_zero {D : Polynomial ℂ} (hD : D ≠ 0) {c : ℂ} (hc : c ≠ 0) :
    D.comp (Polynomial.C c⁻¹ * Polynomial.X) ≠ 0 := by
  intro h
  apply hD
  apply Polynomial.funext
  intro v
  have hu : (D.comp (Polynomial.C c⁻¹ * Polynomial.X)).eval (c * v) = 0 := by rw [h]; simp
  simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at hu
  rw [show c⁻¹ * (c * v) = v by rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]] at hu
  simpa using hu

/-- **Rationality of a germ satisfying a linear polynomial relation on a punctured neighbourhood.**
If `h` is continuous at `0` and `h u * Dp u = Np u` on a punctured neighbourhood of `0` for
polynomials `Np, Dp` with `Dp ≠ 0`, then `h` is the germ of a rational function whose denominator
does not vanish at `0`.

Route: factor out the order of vanishing of `Dp` at `0` (`Dp = X ^ k * E`, `E 0 ≠ 0`). The
continuity of `h` bounds `Np u / u ^ k = h u * E u` near `0`, which forces `X ^ k ∣ Np`; dividing
both sides by `u ^ k` (legitimate on the punctured neighbourhood) and extending the identity to the
puncture by continuity gives the result. -/
lemma rational_germ_core {h : ℂ → ℂ} (hcont : ContinuousAt h (0 : ℂ)) {Np Dp : Polynomial ℂ}
    (hDp_ne : Dp ≠ 0)
    (hmul : ∀ᶠ u in 𝓝[≠] (0 : ℂ), h u * Dp.eval u = Np.eval u) :
    ∃ N₂ D₂ : Polynomial ℂ, D₂.eval 0 ≠ 0 ∧
      ∀ᶠ u in 𝓝 (0 : ℂ), h u * D₂.eval u = N₂.eval u := by
  set k := Dp.rootMultiplicity 0 with hk
  obtain ⟨E, hEfac, hEndvd⟩ :=
    Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd Dp hDp_ne 0
  rw [← hk] at hEfac
  have hE0 : E.eval 0 ≠ 0 := by
    intro h0
    exact hEndvd (Polynomial.dvd_iff_isRoot.mpr h0)
  have hXk : (Polynomial.X : Polynomial ℂ) ^ k ∣ Np := by
    rcases eq_or_ne Np 0 with hNp0 | hNpne
    · rw [hNp0]; exact dvd_zero _
    · have hiff := Polynomial.le_rootMultiplicity_iff (p := Np) hNpne (a := (0 : ℂ)) (n := k)
      have hk_le : k ≤ Np.rootMultiplicity 0 := by
        by_contra hlt
        rw [not_le] at hlt
        set j := Np.rootMultiplicity 0 with hj
        obtain ⟨F, hFfac, hFndvd⟩ :=
          Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd Np hNpne 0
        rw [← hj] at hFfac
        have hF0 : F.eval 0 ≠ 0 := by
          intro h0
          exact hFndvd (Polynomial.dvd_iff_isRoot.mpr h0)
        have hpos : 0 < k - j := by omega
        -- On the punctured neighbourhood, cancel the common factor `u ^ j`.
        have hφ : ∀ᶠ u in 𝓝[≠] (0 : ℂ),
            u ^ (k - j) * h u * E.eval u - F.eval u = 0 := by
          filter_upwards [hmul, self_mem_nhdsWithin] with u hu hu0
          have hu0' : u ≠ 0 := by simpa using hu0
          have hDpe : Dp.eval u = u ^ k * E.eval u := by rw [hEfac]; simp
          have hNpe : Np.eval u = u ^ j * F.eval u := by rw [hFfac]; simp
          rw [hDpe, hNpe] at hu
          have hcancel : u ^ (k - j) * (h u * E.eval u) = F.eval u := by
            apply mul_left_cancel₀ (pow_ne_zero j hu0')
            rw [← hu, ← mul_assoc,
              show u ^ j * u ^ (k - j) = u ^ k by rw [← pow_add, Nat.add_sub_of_le hlt.le]]
            ring
          rw [mul_assoc, hcancel, sub_self]
        have hφc : ContinuousAt
            (fun u : ℂ => u ^ (k - j) * h u * E.eval u - F.eval u) (0 : ℂ) := by
          have hE : ContinuousAt (fun u : ℂ => E.eval u) (0 : ℂ) := by
            have hh := Polynomial.continuousAt_aeval (R := ℂ) (A := ℂ) (p := E) (a := 0)
            simpa [Polynomial.aeval_def] using hh
          have hF : ContinuousAt (fun u : ℂ => F.eval u) (0 : ℂ) := by
            have hh := Polynomial.continuousAt_aeval (R := ℂ) (A := ℂ) (p := F) (a := 0)
            simpa [Polynomial.aeval_def] using hh
          exact (((continuousAt_id.pow (k - j)).mul hcont).mul hE).sub hF
        have hzero := eq_zero_of_nhdsWithin_ne hφc hφ
        have : F.eval 0 = 0 := by simpa [zero_pow (ne_of_gt hpos)] using hzero
        exact hF0 this
      simpa using hiff.mp hk_le
  obtain ⟨N₂, hN₂⟩ := hXk
  refine ⟨N₂, E, hE0, ?_⟩
  -- On the punctured neighbourhood, cancel the common factor `u ^ k`.
  have hev : ∀ᶠ u in 𝓝[≠] (0 : ℂ), h u * E.eval u - N₂.eval u = 0 := by
    filter_upwards [hmul, self_mem_nhdsWithin] with u hu hu0
    have hu0' : u ≠ 0 := by simpa using hu0
    have hDpe : Dp.eval u = u ^ k * E.eval u := by rw [hEfac]; simp
    have hNpe : Np.eval u = u ^ k * N₂.eval u := by rw [hN₂]; simp
    rw [hDpe, hNpe] at hu
    have hu' : u ^ k * (h u * E.eval u) = u ^ k * N₂.eval u := by rw [← hu]; ring
    exact sub_eq_zero.mpr (mul_left_cancel₀ (pow_ne_zero k hu0') hu')
  have hE : ContinuousAt (fun u : ℂ => E.eval u) (0 : ℂ) := by
    have hh := Polynomial.continuousAt_aeval (R := ℂ) (A := ℂ) (p := E) (a := 0)
    simpa [Polynomial.aeval_def] using hh
  have hN₂c : ContinuousAt (fun u : ℂ => N₂.eval u) (0 : ℂ) := by
    have hh := Polynomial.continuousAt_aeval (R := ℂ) (A := ℂ) (p := N₂) (a := 0)
    simpa [Polynomial.aeval_def] using hh
  have hφc : ContinuousAt (fun u : ℂ => h u * E.eval u - N₂.eval u) (0 : ℂ) :=
    (hcont.mul hE).sub hN₂c
  filter_upwards [eventually_eq_zero_of_nhdsWithin_ne hφc hev] with u hu
  exact sub_eq_zero.mp hu

/-- **A germ that agrees near `0` with a rational function after an invertible scaling is rational.** If `g z = h (c * z)` for `z` near `0` with `c ≠ 0`, `h` is continuous at `0`, and `g` satisfies a rational relation `g * D = N` (`D ≠ 0`) on a punctured neighbourhood of `0`, then `h` is the germ of a rational function whose denominator does not vanish at `0`. This is the last step of `rational_of_compact_cycle`: take `g = W ∘ Φ`, `c = eqLam a`. Suggested route: substitute `u = c * z` to get `h u * D(u/c) = N(u/c)` for `u` near `0`, `u ≠ 0`; factor out powers of `X` on both sides (using `ContinuousAt h 0`, which bounds `h` near `0`, to see that no strict pole can occur); extend the resulting identity to the puncture by continuity. -/
theorem rational_germ_of_eventually_eq_comp {h g : ℂ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (hcont : ContinuousAt h 0) {N D : Polynomial ℂ} (hD : D ≠ 0)
    (hg : ∀ᶠ z in 𝓝[≠] (0 : ℂ), g z * D.eval z = N.eval z)
    (hid : ∀ᶠ z in 𝓝 (0 : ℂ), g z = h (c * z)) :
    ∃ N₂ D₂ : Polynomial ℂ, D₂.eval 0 ≠ 0 ∧
      ∀ᶠ u in 𝓝 (0 : ℂ), h u * D₂.eval u = N₂.eval u := by
  set Dp : Polynomial ℂ := D.comp (Polynomial.C c⁻¹ * Polynomial.X) with hDp
  set Np : Polynomial ℂ := N.comp (Polynomial.C c⁻¹ * Polynomial.X) with hNp
  have hDp_ne : Dp ≠ 0 := hDp ▸ comp_C_mul_X_ne_zero hD hc
  -- Substitute `u = c⁻¹ * z` into the relation `g z * D z = N z`.
  have hmul : ∀ᶠ u in 𝓝[≠] (0 : ℂ), h u * Dp.eval u = Np.eval u := by
    have hmul_z : ∀ᶠ z in 𝓝[≠] (0 : ℂ), h (c * z) * D.eval z = N.eval z := by
      filter_upwards [hg, hid.filter_mono nhdsWithin_le_nhds] with z hz1 hz2
      rw [← hz2]; exact hz1
    have hρ : Tendsto (fun u : ℂ => c⁻¹ * u) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
      change Tendsto (fun u : ℂ => c⁻¹ * u) (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ) ⊓ 𝓟 ({0}ᶜ))
      rw [tendsto_inf]
      refine ⟨?_, ?_⟩
      · have hcont' : ContinuousAt (fun u : ℂ => c⁻¹ * u) (0 : ℂ) := by fun_prop
        have hh := continuousAt_iff_punctured_nhds.mp hcont'
        simpa only [mul_zero] using hh
      · rw [tendsto_principal]
        filter_upwards [self_mem_nhdsWithin] with u hu
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hu ⊢
        exact fun hh => hu ((mul_eq_zero.mp hh).resolve_left (inv_ne_zero hc))
    have := hρ.eventually hmul_z
    filter_upwards [this] with u hu
    rw [show c * (c⁻¹ * u) = u by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]] at hu
    simpa only [hDp, hNp, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X] using hu
  exact rational_germ_core hcont hDp_ne hmul

end Work.EQ
