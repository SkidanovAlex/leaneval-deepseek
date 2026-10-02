import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Set Complex

/-! ### Auxiliary facts about the unit circle and `ℝ` -/

/-- For a point `z` of the unit circle, `exp (arg z * I) = z`. -/
private lemma circleAux_exp_arg_mul_I {z : ℂ} (hz : z ∈ Metric.sphere (0 : ℂ) 1) :
    Complex.exp (z.arg * Complex.I) = z := by
  have h := Complex.norm_mul_exp_arg_mul_I z
  rw [mem_sphere_zero_iff_norm.mp hz] at h
  simpa using h

/-- A preconnected subset of `ℝ` contained in the integers is a subsingleton. -/
private lemma circleAux_preconnected_subsingleton_intCast {B : Set ℝ} (hB : IsPreconnected B)
    (hsub : B ⊆ Set.range ((↑) : ℤ → ℝ)) : B.Subsingleton := by
  have key : ∀ a ∈ B, ∀ b ∈ B, a < b → False := by
    intro a ha b hb hab
    obtain ⟨m, hm⟩ := hsub ha
    obtain ⟨n, hn⟩ := hsub hb
    have hmn : ((m : ℝ)) < (n : ℝ) := by
      rw [← hm, ← hn] at hab
      exact hab
    have hmn' : m < n := by exact_mod_cast hmn
    have hle : ((m : ℝ)) + 1 ≤ (n : ℝ) := by
      exact_mod_cast (by omega : m + 1 ≤ n)
    have ht : ((m : ℝ) + 1 / 2) ∈ B := by
      have h1 : ((m : ℝ)) ∈ B := hm ▸ ha
      have h2 : ((n : ℝ)) ∈ B := hn ▸ hb
      exact hB.ordConnected.out h1 h2 ⟨by linarith, by linarith⟩
    obtain ⟨k, hk⟩ := hsub ht
    have hk' : (k : ℝ) - (m : ℝ) = 1 / 2 := by rw [hk]; ring
    have h2 : ((2 * (k - m) : ℤ) : ℝ) = 1 := by
      push_cast
      linarith
    have h3 : (2 * (k - m) : ℤ) = 1 := by exact_mod_cast h2
    omega
  intro a ha b hb
  rcases lt_trichotomy a b with h | h | h
  · exact (key a ha b hb h).elim
  · exact h
  · exact (key b hb a ha h).elim

/-- A continuous integer valued function on a preconnected subset of `ℝ` is constant there. -/
private lemma circleAux_preconnected_eq_of_int_valued {B : Set ℝ} (hB : IsPreconnected B)
    {g : ℝ → ℝ} (hg : ContinuousOn g B) (hint : ∀ x ∈ B, ∃ m : ℤ, g x = (m : ℝ))
    {x y : ℝ} (hx : x ∈ B) (hy : y ∈ B) : g x = g y := by
  have hsub : g '' B ⊆ Set.range ((↑) : ℤ → ℝ) := by
    rintro u ⟨z, hz, rfl⟩
    obtain ⟨m, hm⟩ := hint z hz
    exact ⟨m, hm.symm⟩
  have hss : (g '' B).Subsingleton :=
    circleAux_preconnected_subsingleton_intCast (hB.image g hg) hsub
  exact hss (mem_image_of_mem g hx) (mem_image_of_mem g hy)

/-- **Core step.**  A compact preconnected nonempty subset of the unit circle avoiding `-1`
and mapped into itself by a rotation `ζ ≠ 1` does not exist. -/
private lemma circleAux_core {S : Set ℂ} (hSsph : S ⊆ Metric.sphere (0 : ℂ) 1)
    (hcpt : IsCompact S) (hpre : IsPreconnected S) (hne : S.Nonempty)
    (hm1 : (-1 : ℂ) ∉ S) {ζ : ℂ} (hζsph : ζ ∈ Metric.sphere (0 : ℂ) 1) (hζ : ζ ≠ 1)
    (hinv : ∀ d ∈ S, ζ * d ∈ S) : False := by
  have hSlit : S ⊆ Complex.slitPlane := by
    intro d hd
    rw [Complex.mem_slitPlane_iff]
    by_contra h
    push Not at h
    obtain ⟨hre, him⟩ := h
    have hd1 : d = -1 := by
      have hnorm : ‖d‖ = 1 := mem_sphere_zero_iff_norm.mp (hSsph hd)
      have hns : d.re ^ 2 = 1 := by
        have h1 : Complex.normSq d = 1 := by
          rw [Complex.normSq_eq_norm_sq, hnorm]; norm_num
        rw [Complex.normSq_apply, him] at h1
        nlinarith [h1]
      have hre' : d.re = -1 := by
        rcases sq_eq_one_iff.mp hns with h2 | h2
        · exfalso; rw [h2] at hre; norm_num at hre
        · exact h2
      apply Complex.ext <;> simp [hre', him]
    exact hm1 (hd1 ▸ hd)
  have harg_cont : ContinuousOn Complex.arg S := Complex.continuousOn_arg.mono hSlit
  set A : Set ℝ := Complex.arg '' S with hA
  have hA_pre : IsPreconnected A := hpre.image Complex.arg harg_cont
  have hA_cpt : IsCompact A := hcpt.image_of_continuousOn harg_cont
  have hA_ne : A.Nonempty := hne.image Complex.arg
  have hA_sub : A ⊆ Ioo (-Real.pi) Real.pi := by
    rintro s ⟨d, hd, rfl⟩
    have hd1 : d ≠ -1 := fun h => hm1 (h ▸ hd)
    refine ⟨Complex.neg_pi_lt_arg _, lt_of_le_of_ne (Complex.arg_le_pi _) (fun h => hd1 ?_)⟩
    rw [← circleAux_exp_arg_mul_I (hSsph hd), h, Complex.exp_pi_mul_I]
  have hA_closed : IsClosed A := hA_cpt.isClosed
  have hbdd_below : BddBelow A := ⟨-Real.pi, fun s hs => (hA_sub hs).1.le⟩
  have hbdd_above : BddAbove A := ⟨Real.pi, fun s hs => (hA_sub hs).2.le⟩
  obtain ⟨α, hαA, hαle⟩ : ∃ α : ℝ, α ∈ A ∧ ∀ s ∈ A, α ≤ s :=
    ⟨sInf A, hA_closed.csInf_mem hA_ne hbdd_below, fun s hs => csInf_le hbdd_below hs⟩
  obtain ⟨β, hβA, hβle⟩ : ∃ β : ℝ, β ∈ A ∧ ∀ s ∈ A, s ≤ β :=
    ⟨sSup A, hA_closed.csSup_mem hA_ne hbdd_above, fun s hs => le_csSup hbdd_above hs⟩
  set Φ : ℝ → ℂ := fun t => Complex.exp (t * Complex.I) with hΦdef
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, Φ θ = ζ :=
    ⟨ζ.arg, by
      change Complex.exp (ζ.arg * Complex.I) = ζ
      exact circleAux_exp_arg_mul_I hζsph⟩
  have hΦ_add : ∀ a b : ℝ, Φ (a + b) = Φ a * Φ b := by
    intro a b
    change Complex.exp (((a + b : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((a : ℂ) * Complex.I) * Complex.exp ((b : ℂ) * Complex.I)
    rw [show ((a + b : ℝ) : ℂ) * Complex.I =
        (a : ℂ) * Complex.I + (b : ℂ) * Complex.I by push_cast; ring, Complex.exp_add]
  have hΦ_mem : ∀ t ∈ A, Φ t ∈ S := by
    rintro t ⟨d, hd, rfl⟩
    change Complex.exp (d.arg * Complex.I) ∈ S
    rw [circleAux_exp_arg_mul_I (hSsph hd)]
    exact hd
  set T : ℝ → ℝ := fun t => (ζ * Φ t).arg with hTdef
  have hT_cont : ContinuousOn T A := by
    have hcont : Continuous (fun t : ℝ => ζ * Φ t) := by
      change Continuous (fun t : ℝ => ζ * Complex.exp (t * Complex.I))
      fun_prop
    have hmap : MapsTo (fun t : ℝ => ζ * Φ t) A Complex.slitPlane :=
      fun t ht => hSlit (hinv _ (hΦ_mem t ht))
    exact Complex.continuousOn_arg.comp hcont.continuousOn hmap
  have hT_mem : ∀ t ∈ A, T t ∈ A :=
    fun t ht => ⟨ζ * Φ t, hinv _ (hΦ_mem t ht), rfl⟩
  have hT_rel : ∀ t ∈ A, ∃ m : ℤ, T t = θ + t + (m : ℝ) * (2 * Real.pi) := by
    intro t ht
    have hζΦ : ζ * Φ t ∈ Metric.sphere (0 : ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_mul, mem_sphere_zero_iff_norm.mp hζsph,
        mem_sphere_zero_iff_norm.mp (hSsph (hΦ_mem t ht)), one_mul]
    have h1 : Φ (T t) = ζ * Φ t := by
      change Complex.exp (((ζ * Φ t).arg) * Complex.I) = ζ * Φ t
      exact circleAux_exp_arg_mul_I hζΦ
    have h2 : Φ (θ + t) = ζ * Φ t := by rw [hΦ_add, hθ]
    have h3 : Φ (T t) = Φ (θ + t) := h1.trans h2.symm
    have hcoe : (↑(Circle.exp (T t)) : ℂ) = ↑(Circle.exp (θ + t)) := by
      rw [Circle.coe_exp, Circle.coe_exp]
      exact h3
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp (Circle.coe_inj.mp hcoe)
    exact ⟨m, hm⟩
  set G : ℝ → ℝ := fun t => (T t - t - θ) / (2 * Real.pi) with hGdef
  have hG_cont : ContinuousOn G A := by
    rw [hGdef]
    exact ((hT_cont.sub continuousOn_id).sub continuousOn_const).div_const _
  have hG_int : ∀ t ∈ A, ∃ m : ℤ, G t = (m : ℝ) := by
    intro t ht
    obtain ⟨m, hm⟩ := hT_rel t ht
    refine ⟨m, ?_⟩
    have hnum : θ + t + (m : ℝ) * (2 * Real.pi) - t - θ = (m : ℝ) * (2 * Real.pi) := by ring
    change (T t - t - θ) / (2 * Real.pi) = (m : ℝ)
    rw [hm, hnum, mul_div_cancel_right₀ _ (by positivity : (2 * Real.pi : ℝ) ≠ 0)]
  have hGconst : G α = G β :=
    circleAux_preconnected_eq_of_int_valued hA_pre hG_cont hG_int hαA hβA
  have hdiff : T α - α = T β - β := by
    have h := hGconst
    rw [hGdef] at h
    have h2π : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have h' := (div_left_inj' h2π).mp h
    linarith
  have h1 : α ≤ T α := hαle (T α) (hT_mem α hαA)
  have h2 : T β ≤ β := hβle (T β) (hT_mem β hβA)
  have hc0 : T α - α = 0 := le_antisymm (by linarith) (by linarith)
  have hGα : G α = -θ / (2 * Real.pi) := by
    change (T α - α - θ) / (2 * Real.pi) = -θ / (2 * Real.pi)
    rw [show T α - α - θ = -θ by linarith]
  obtain ⟨m, hm⟩ := hG_int α hαA
  have hθm : θ = -(m : ℝ) * (2 * Real.pi) := by
    rw [hGα] at hm
    have h2π : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have h4 := congrArg (fun t : ℝ => t * (2 * Real.pi)) hm
    rw [div_mul_cancel₀ _ h2π] at h4
    linarith
  have hzeta : ζ = 1 := by
    have h1 : Complex.exp (θ * Complex.I) = 1 := by
      rw [hθm, Complex.exp_eq_one_iff]
      exact ⟨-m, by push_cast; ring⟩
    rw [← h1]
    exact hθ.symm
  exact hζ hzeta

/-- **A continuum in the unit circle invariant under a nontrivial finite-order rotation is the
whole circle.**  If `L ⊆ ℂ` is compact, preconnected and nonempty, contained in the unit circle,
and `z` is a `q`-th root of unity (`q > 0`, `z ≠ 1`) with `z * L ⊆ L`, then
`L = Metric.sphere (0:ℂ) 1`.

Hint. Suppose `L ≠ sphere 0 1`, pick `z₁ ∉ L`, and lift through the homeomorphism
`Φ : (a, a+2π) ≅ sphere 0 1 ∖ {z₁}`, `Φ s = exp (s * I)`: then `L = Φ '' (Icc α β)` for a closed
interval `[α,β]` with `β - α < 2π` (a compact preconnected subset of `ℝ` is a closed interval).
Since `z^q = 1`, `L = z^q L ⊆ z L ⊆ L`, so `z L = L` and `τ s = Φ⁻¹ (z * Φ s)` is a well defined
map `Icc α β → Icc α β` with `Φ (τ s) = z * Φ s`, i.e. `τ s ≡ s + θ (mod 2π)` where `z = Φ θ`.
Continuity of `s ↦ τ s - s - θ` and integrality force `τ s = s + θ + 2πk` with `k` constant, while
`τ (Icc α β) = Icc α β` gives `τ α ≥ α` and `τ β ≤ β`; thus `θ + 2πk = 0` and `z = Φ θ = 1`,
contradicting `hz1`. -/
theorem eqSphereOfPreconnectedOfPowEqOne {L : Set ℂ} {z : ℂ} {q : ℕ}
    (hLcpt : IsCompact L) (hLpre : IsPreconnected L) (hLne : L.Nonempty)
    (hLsph : L ⊆ Metric.sphere (0 : ℂ) 1) (hz : ‖z‖ = 1) (hq : 0 < q) (hzq : z ^ q = 1)
    (hz1 : z ≠ 1) (hinv : ∀ d ∈ L, z * d ∈ L) : L = Metric.sphere (0 : ℂ) 1 := by
  have _ := hq
  have _ := hzq
  by_contra hne
  have hex : ∃ p : ℂ, p ∈ Metric.sphere (0 : ℂ) 1 ∧ p ∉ L := by
    by_contra h
    push Not at h
    exact hne (le_antisymm hLsph fun d hd => h d hd)
  obtain ⟨p, hp_sph, hpL⟩ := hex
  set W : ℂ := -p⁻¹ with hW
  have hW_sph : W ∈ Metric.sphere (0 : ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, hW, norm_neg, norm_inv, mem_sphere_zero_iff_norm.mp hp_sph,
      inv_one]
  set S : Set ℂ := (fun d : ℂ => W * d) '' L with hS
  have hcW : Continuous (fun d : ℂ => W * d) := by fun_prop
  have hS_cpt : IsCompact S := by
    rw [hS]
    exact IsCompact.image hLcpt hcW
  have hS_pre : IsPreconnected S := by
    rw [hS]
    exact IsPreconnected.image hLpre _ hcW.continuousOn
  have hS_ne : S.Nonempty := by
    rw [hS]
    exact hLne.image _
  have hS_sph : S ⊆ Metric.sphere (0 : ℂ) 1 := by
    rintro d ⟨e, he, rfl⟩
    rw [mem_sphere_zero_iff_norm, norm_mul, mem_sphere_zero_iff_norm.mp hW_sph,
      mem_sphere_zero_iff_norm.mp (hLsph he), one_mul]
  have hS_m1 : (-1 : ℂ) ∉ S := by
    rintro ⟨d, hd, hwe⟩
    have hp0 : p ≠ 0 := by
      intro h
      have hpn := mem_sphere_zero_iff_norm.mp hp_sph
      rw [h, norm_zero] at hpn
      norm_num at hpn
    have h1 : p⁻¹ * d = 1 := by
      change -p⁻¹ * d = -1 at hwe
      rw [neg_mul] at hwe
      exact neg_inj.mp hwe
    have h2 : d = p := by
      have h3 := congrArg (fun t : ℂ => p * t) h1
      rw [mul_one, ← mul_assoc, mul_inv_cancel₀ hp0, one_mul] at h3
      exact h3
    exact hpL (h2 ▸ hd)
  have hinvS : ∀ d ∈ S, z * d ∈ S := by
    rintro d ⟨e, he, rfl⟩
    exact ⟨z * e, hinv e he, by ring⟩
  exact circleAux_core hS_sph hS_cpt hS_pre hS_ne hS_m1
    (mem_sphere_zero_iff_norm.mpr hz) hz1 hinvS

end Work.LandLeaves
