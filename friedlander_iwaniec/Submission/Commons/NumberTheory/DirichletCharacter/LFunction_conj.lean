import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.NumberTheory.LSeries.DirichletContinuation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Conjugation of Dirichlet L-functions

The conjugation identity for the (analytic continuation of the) Dirichlet
L-function of a non-trivial character:

    conj (L(s, χ)) = L(conj s, χ⁻¹)          (χ ≠ 1)

**Proof route**:

1. `conj_cpow_ofReal_pos`: conjugation commutes with complex powers of
   positive reals (`Complex.cpow_conj`, the base `(x : ℂ)` has argument `0 ≠ π`);
2. `star_apply_char`: conjugation commutes with the character: for every
   `a : ZMod N`, `conj (χ a) = (χ⁻¹ a)` — units via `‖χ a‖ = 1`
   (`DirichletCharacter.unit_norm_eq_one`) so `conj z = z⁻¹`, and
   `χ⁻¹ a = (χ a)⁻¹` by multiplicativity + `MulChar.inv_apply` +
   `Ring.inverse_unit`; non-units map to `0` on both sides;
3. `conj_LSeries_char`: on the convergence half-plane `1 < re w`, conjugation
   passes through the naive Dirichlet series termwise
   (`Summable.hasSum` + `HasSum.star` + termwise
   `conj (f n / n^w) = g n / n^(conj w)`), giving

       conj (LSeries (χ·) w) = LSeries ((χ⁻¹)·) (conj w);

4. `starComp`, `hasDerivAt_star_comp`, `differentiable_starComp`: the function
   `s ↦ conj (f (conj s))` of a holomorphic `f` is holomorphic (anti-hol ∘ hol
   ∘ anti-hol) — proved by the little-`o` characterization of `HasDerivAt`
   (`hasDerivAt_iff_isLittleO`, `isLittleO_iff`) and the norm-preservation
   `‖conj w‖ = ‖w‖`;
5. identity theorem (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` + the
   `Differentiable ⇒ AnalyticOnNhd` theorem) applied to
   `starComp (χ.LFunction)` and `(χ⁻¹).LFunction`, which agree on the open
   half-plane `{s | 1 < s.re}` (step 3 + `LFunction_eq_LSeries` twice).
-/

open Complex DirichletCharacter Filter
open scoped Real Topology BigOperators
set_option autoImplicit false

namespace Commons.NumberTheory.DirichletCharacter

noncomputable section

variable {N : ℕ} [NeZero N]

/-- Conjugation commutes with complex powers of a positive real base. -/
lemma conj_cpow_ofReal_pos (x : ℝ) (hx : 0 < x) (z : ℂ) :
    (starRingEnd ℂ) ((x : ℂ) ^ z) = (x : ℂ) ^ ((starRingEnd ℂ) z) := by
  have harg : ((x : ℂ).arg ≠ Real.pi) := by
    rw [Complex.arg_ofReal_of_nonneg (le_of_lt hx)]
    exact Real.pi_ne_zero.symm
  have h := Complex.cpow_conj (x : ℂ) z harg
  rw [Complex.conj_ofReal] at h
  exact h.symm

/-- Conjugation commutes with the character: `conj (χ a) = χ⁻¹ a`. -/
lemma star_apply_char (χ : DirichletCharacter ℂ N) (a : ZMod N) :
    (starRingEnd ℂ) (χ a) = χ⁻¹ a := by
  by_cases hu : IsUnit a
  · rcases hu with ⟨u, rfl⟩
    -- unit case: conj(χu) = (χu)⁻¹ = χ(u⁻¹) = χ⁻¹(u)
    have hnorm : ‖χ (u : ZMod N)‖ = 1 := DirichletCharacter.unit_norm_eq_one χ u
    have hprod0 : χ (u : ZMod N) * χ (((u⁻¹ : (ZMod N)ˣ) : ZMod N)) = 1 := by
      have hmap : χ ((u : ZMod N) * ((u⁻¹ : (ZMod N)ˣ) : ZMod N)) =
          χ (u : ZMod N) * χ (((u⁻¹ : (ZMod N)ˣ) : ZMod N)) := by
        exact map_mul (χ : ZMod N →* ℂ) (u : ZMod N) ((u⁻¹ : (ZMod N)ˣ) : ZMod N)
      have hu1 : (u : ZMod N) * (((u⁻¹ : (ZMod N)ˣ)) : ZMod N) = 1 := by
        calc
          (u : ZMod N) * (((u⁻¹ : (ZMod N)ˣ)) : ZMod N) = (((u * u⁻¹ : (ZMod N)ˣ)) : ZMod N) := by
            rw [← Units.val_mul u (u⁻¹ : (ZMod N)ˣ)]
          _ = 1 := by
            rw [mul_inv_cancel u]
            simp
      calc
        χ (u : ZMod N) * χ (((u⁻¹ : (ZMod N)ˣ) : ZMod N)) = χ ((u : ZMod N) * ((u⁻¹ : (ZMod N)ˣ) : ZMod N)) := hmap.symm
        _ = χ (1 : ZMod N) := by rw [hu1]
        _ = 1 := map_one (χ : ZMod N →* ℂ)
    have hconj : (starRingEnd ℂ) (χ (u : ZMod N)) = (χ (u : ZMod N))⁻¹ := by
      have hprod : χ (u : ZMod N) * (starRingEnd ℂ) (χ (u : ZMod N)) = 1 := by
        have hmc : χ (u : ZMod N) * (starRingEnd ℂ) (χ (u : ZMod N)) = ↑‖χ (u : ZMod N)‖ ^ 2 :=
          Complex.mul_conj' (χ (u : ZMod N))
        rw [hmc, hnorm]
        norm_num
      exact eq_inv_of_mul_eq_one_right hprod
    have hinv : (χ (u : ZMod N))⁻¹ = χ (((u⁻¹ : (ZMod N)ˣ) : ZMod N)) := by
      exact (eq_inv_of_mul_eq_one_right hprod0).symm
    have hchiinv : χ (((u⁻¹ : (ZMod N)ˣ) : ZMod N)) = χ⁻¹ (u : ZMod N) := by
      rw [MulChar.inv_apply]
      rw [Ring.inverse_unit]
    calc
      (starRingEnd ℂ) (χ (u : ZMod N)) = (χ (u : ZMod N))⁻¹ := hconj
      _ = χ (((u⁻¹ : (ZMod N)ˣ) : ZMod N)) := hinv
      _ = χ⁻¹ (u : ZMod N) := hchiinv
  · have hχ0 : χ a = 0 := MulChar.map_nonunit χ hu
    have hχinv0 : χ⁻¹ a = 0 := MulChar.map_nonunit (χ⁻¹) hu
    simp [hχ0, hχinv0]

/-- Termwise conjugation of the L-series summand. -/
lemma conj_term_char (χ : DirichletCharacter ℂ N) {w : ℂ} (_hw : 1 < w.re) (n : ℕ) :
    (starRingEnd ℂ) (LSeries.term (fun m : ℕ => χ (m : ZMod N)) w n) =
      LSeries.term (fun m : ℕ => χ⁻¹ (m : ZMod N)) ((starRingEnd ℂ) w) n := by
  rw [LSeries.term_def, LSeries.term_def]
  by_cases hn : n = 0
  · simp [hn]
  · have hnz : n ≠ 0 := hn
    simp [hnz]
    have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hnz)
    have hc := star_apply_char χ (n : ZMod N)
    have hcp := conj_cpow_ofReal_pos (n : ℝ) hpos w
    have hcpc : (starRingEnd ℂ) (((n : ℕ) : ℂ) ^ w) = (((n : ℕ) : ℂ) ^ (starRingEnd ℂ) w) := by
      simpa using hcp
    rw [hc, hcpc]

/-- On the convergence half-plane conjugation commutes with the L-series. -/
lemma conj_LSeries_char (χ : DirichletCharacter ℂ N) {w : ℂ} (hw : 1 < w.re) :
    (starRingEnd ℂ) (LSeries (fun n : ℕ => χ (n : ZMod N)) w) =
      LSeries (fun n : ℕ => χ⁻¹ (n : ZMod N)) ((starRingEnd ℂ) w) := by
  let f : ℕ → ℂ := fun n => χ (n : ZMod N)
  let g : ℕ → ℂ := fun n => χ⁻¹ (n : ZMod N)
  have hsum : LSeriesSummable f w := by
    dsimp [f]
    exact ZMod.LSeriesSummable_of_one_lt_re (fun a : ZMod N => (χ a : ℂ)) hw
  have htsum : (starRingEnd ℂ) (∑' n : ℕ, LSeries.term f w n) = ∑' n : ℕ, (starRingEnd ℂ) (LSeries.term f w n) := by
    exact (hsum.hasSum.star).tsum_eq.symm
  calc
    (starRingEnd ℂ) (LSeries f w)
        = (starRingEnd ℂ) (∑' n : ℕ, LSeries.term f w n) := by rfl
    _ = ∑' n : ℕ, (starRingEnd ℂ) (LSeries.term f w n) := htsum
    _ = ∑' n : ℕ, LSeries.term g ((starRingEnd ℂ) w) n := by
          apply tsum_congr
          intro n
          exact conj_term_char χ hw n
    _ = LSeries g ((starRingEnd ℂ) w) := by rfl

/-- The conjugated-in-`s` function: `s ↦ conj(f (conj s))`. -/
def starComp (f : ℂ → ℂ) : ℂ → ℂ := fun s => (starRingEnd ℂ) (f ((starRingEnd ℂ) s))

/-- Conjugation of a holomorphic function is holomorphic (anti-hol ∘ hol ∘ anti-hol). -/
lemma hasDerivAt_star_comp {f : ℂ → ℂ} {c z : ℂ} (hf : HasDerivAt f c ((starRingEnd ℂ) z)) :
    HasDerivAt (starComp f) ((starRingEnd ℂ) c) z := by
  rw [hasDerivAt_iff_isLittleO] at hf ⊢
  rw [Asymptotics.isLittleO_iff] at hf ⊢
  · intro ε hε
    have hfε : ∀ᶠ x'' in 𝓝 ((starRingEnd ℂ) z),
        ‖f x'' - f ((starRingEnd ℂ) z) - (x'' - ((starRingEnd ℂ) z)) • c‖ ≤ ε * ‖x'' - ((starRingEnd ℂ) z)‖ :=
      hf hε
    have hcstar : Continuous (starRingEnd ℂ) := Complex.continuous_conj
    have ht : Tendsto (starRingEnd ℂ) (𝓝 z) (𝓝 ((starRingEnd ℂ) z)) := hcstar.tendsto z
    have hpull : ∀ᶠ x' in 𝓝 z,
        ‖f ((starRingEnd ℂ) x') - f ((starRingEnd ℂ) z) - (((starRingEnd ℂ) x') - ((starRingEnd ℂ) z)) • c‖ ≤
          ε * ‖((starRingEnd ℂ) x') - ((starRingEnd ℂ) z)‖ := by
      have hpre : (starRingEnd ℂ) ⁻¹' {x'' : ℂ |
          ‖f x'' - f ((starRingEnd ℂ) z) - (x'' - ((starRingEnd ℂ) z)) • c‖ ≤
            ε * ‖x'' - ((starRingEnd ℂ) z)‖} ∈ 𝓝 z := ht hfε
      exact hpre
    filter_upwards [hpull] with x' hx'
    have hmain : (starComp f) x' - (starComp f) z - (x' - z) • (starRingEnd ℂ) c =
        (starRingEnd ℂ) (f ((starRingEnd ℂ) x') - f ((starRingEnd ℂ) z)
          - (((starRingEnd ℂ) x') - ((starRingEnd ℂ) z)) • c) := by
      unfold starComp
      rw [map_sub (starRingEnd ℂ)]
      rw [← map_sub (starRingEnd ℂ)]
      congr 1
      have hsm : (starRingEnd ℂ) ((((starRingEnd ℂ) x' - (starRingEnd ℂ) z)) • c) = (x' - z) • (starRingEnd ℂ) c := by
        rw [smul_eq_mul, smul_eq_mul]
        rw [map_mul (starRingEnd ℂ)]
        rw [← map_sub (starRingEnd ℂ)]
        simp
      exact hsm.symm
    calc
      ‖(starComp f) x' - (starComp f) z - (x' - z) • (starRingEnd ℂ) c‖
          = ‖f ((starRingEnd ℂ) x') - f ((starRingEnd ℂ) z) - (((starRingEnd ℂ) x') - ((starRingEnd ℂ) z)) • c‖ := by
            rw [hmain]
            exact Complex.norm_conj _
      _ ≤ ε * ‖((starRingEnd ℂ) x') - ((starRingEnd ℂ) z)‖ := hx'
      _ = ε * ‖x' - z‖ := by
            congr 1
            rw [← map_sub (starRingEnd ℂ)]
            exact Complex.norm_conj (x' - z)

/-- `starComp f` of a differentiable function is differentiable. -/
lemma differentiable_starComp {f : ℂ → ℂ} (hf : Differentiable ℂ f) : Differentiable ℂ (starComp f) := by
  intro z
  have hd : HasDerivAt f (deriv f ((starRingEnd ℂ) z)) ((starRingEnd ℂ) z) :=
    (hf ((starRingEnd ℂ) z)).hasDerivAt
  exact (hasDerivAt_star_comp hd).differentiableAt

/-- Conjugation identity on the convergence half-plane. -/
lemma starL_apply_eq (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    starComp (χ.LFunction) s = (χ⁻¹).LFunction s := by
  unfold starComp
  have hsstar : 1 < (((starRingEnd ℂ) s).re) := by
    rw [starRingEnd_apply]
    simpa [Complex.conj_re] using hs
  have h1 := DirichletCharacter.LFunction_eq_LSeries χ hsstar
  have h2 := DirichletCharacter.LFunction_eq_LSeries (χ⁻¹) hs
  calc
    (starRingEnd ℂ) (χ.LFunction ((starRingEnd ℂ) s))
        = (starRingEnd ℂ) (LSeries (fun n : ℕ => χ (n : ZMod N)) ((starRingEnd ℂ) s)) := by rw [h1]
    _ = LSeries (fun n : ℕ => χ⁻¹ (n : ZMod N)) s := by
          have hc := conj_LSeries_char χ hsstar
          simpa using hc
    _ = (χ⁻¹).LFunction s := by rw [h2]

/-- **Conjugation of the Dirichlet L-function**: `conj (L(s,χ)) = L(conj s, χ⁻¹)`. -/
theorem LFunction_conj {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ) :
    (starRingEnd ℂ) (χ.LFunction s) = (χ⁻¹).LFunction ((starRingEnd ℂ) s) := by
  let F : ℂ → ℂ := starComp (χ.LFunction)
  let G : ℂ → ℂ := (χ⁻¹).LFunction
  have hχinv_ne : χ⁻¹ ≠ 1 := by
    intro h1
    have hχ1 : χ = 1 := by
      have hh := congrArg (fun ψ : DirichletCharacter ℂ N => ψ⁻¹) h1
      simpa using hh
    exact hχ hχ1
  have hF : AnalyticOnNhd ℂ F (Set.univ : Set ℂ) := by
    intro z hz
    exact Differentiable.analyticAt (differentiable_starComp (DirichletCharacter.differentiable_LFunction hχ)) z
  have hG : AnalyticOnNhd ℂ G (Set.univ : Set ℂ) := by
    intro z hz
    exact Differentiable.analyticAt (DirichletCharacter.differentiable_LFunction hχinv_ne) z
  let z₀ : ℂ := (2 : ℂ)
  have hz₀re : (1 : ℝ) < z₀.re := by
    dsimp [z₀]
    norm_num
  have hset : {x : ℂ | 1 < x.re} ∈ 𝓝 z₀ := (isOpen_lt continuous_const continuous_re).mem_nhds hz₀re
  have hev : F =ᶠ[𝓝 z₀] G := by
    filter_upwards [hset] with x hx
    dsimp [F, G]
    exact starL_apply_eq χ hx
  have hEqOn := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (U := (Set.univ : Set ℂ)) hF hG
    isPreconnected_univ (Set.mem_univ z₀) hev
  have hps := hEqOn (Set.mem_univ ((starRingEnd ℂ) s))
  dsimp [F, G] at hps
  unfold starComp at hps
  simpa [star_star] using hps

end

end Commons.NumberTheory.DirichletCharacter