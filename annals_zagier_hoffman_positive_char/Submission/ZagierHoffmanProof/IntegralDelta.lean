import Submission.ZagierHoffmanProof.Endgame2
import Submission.ZagierHoffmanProof.DegTheta
import Submission.ZagierHoffmanProof.Rationality
import Submission.ZagierHoffmanProof.Solve64

/-!
# The integrality (`denominator clearing`) step between the `∅`-row and `kuanLin_degree`

`PLAN.md` §«SESSION 351» §«continued 12» specifies the target lemma `integral_delta`: from the
cleared `∅`-row of the two-term datum,
`Q · σ(P_[]) = σ(Q) · W^w · (P_[] + P_j + Q·A₁·H_w)`  (`W = X - C θ^q`),
produce `δ, Fp ∈ ambA F 0[X]` with `σ(δ) = δ·W^w + Fp`; then
`KuanLin.coeff_mem_ambA_zero_of_kuanLin` and `DegTheta.kuanLin_degree` apply verbatim.

This file starts with the smallest atom of that step (the `hn₀` hypothesis of `kuanLin_degree`), then
will carry the potential-denominator argument (as in `Rationality.evalSeriesGen_mem_ambK_of_frobInv`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
open Polynomial
open scoped WithZero Topology Classical

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ **The `hn₀` atom of `kuanLin_degree`**: for any polynomial `δ`, some index `n₀` attains the
maximum of `degTheta F (δ.coeff ·)` (over `range (δ.natDegree + 1)`; outside that range the
coefficients vanish and `degTheta F 0 = 0`). -/
lemma exists_degTheta_coeff_max (δ : Polynomial (Ambient F)) :
    ∃ n₀ : ℕ, ∀ n : ℕ, degTheta F (δ.coeff n) ≤ degTheta F (δ.coeff n₀) := by
  obtain ⟨n₀, -, hn₀⟩ := Finset.exists_max_image (Finset.range (δ.natDegree + 1))
    (fun n => degTheta F (δ.coeff n))
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
  refine ⟨n₀, fun n => ?_⟩
  by_cases hn : n ≤ δ.natDegree
  · exact hn₀ n (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), degTheta_zero]
    exact Nat.zero_le _


/-! ## §2. The potential-denominator ideal at the polynomial level (step 1 of §«continued 12») -/

/-- **The potential-denominator ideal** of the pair `(Pl, Q)`, lifted from
`Rationality.denIdeal` from the power-series to the polynomial level: the ideal of those `H` for
which `Pl · H` is a multiple of `Q` (by a *polynomial*). -/
noncomputable def denIdealPoly (Pl Q : Polynomial (Ambient F)) : Ideal (Polynomial (Ambient F)) where
  carrier := {H | ∃ G : Polynomial (Ambient F), Pl * H = G * Q}
  zero_mem' := ⟨0, by ring⟩
  add_mem' := by
    rintro H H' ⟨G, hG⟩ ⟨G', hG'⟩
    refine ⟨G + G', ?_⟩
    calc Pl * (H + H') = Pl * H + Pl * H' := by ring
      _ = G * Q + G' * Q := by rw [hG, hG']
      _ = (G + G') * Q := by ring
  smul_mem' := by
    rintro A H ⟨G, hG⟩
    refine ⟨A * G, ?_⟩
    calc Pl * (A * H) = A * (Pl * H) := by ring
      _ = A * (G * Q) := by rw [hG]
      _ = (A * G) * Q := by ring

/-- `Q` is always a potential denominator of `(Pl, Q)`. -/
lemma mem_denIdealPoly_self (Pl Q : Polynomial (Ambient F)) : Q ∈ denIdealPoly F Pl Q :=
  ⟨Pl, by ring⟩

/-- Every `Pl · H` multiple of `Q` is witnessed by `H ∈ denIdealPoly`. -/
lemma mem_denIdealPoly_iff {Pl Q H : Polynomial (Ambient F)} :
    H ∈ denIdealPoly F Pl Q ↔ ∃ G : Polynomial (Ambient F), Pl * H = G * Q := Iff.rfl



/-- ★★ **The coefficient-level output of `Rationality.evalSeriesGen_mem_ambK_of_frobInv`**
(Dac/Chang Prop 2.2.1 in the (1)-form): a common denominator `b` of `f/Q` with `F_q`-coefficients. -/
lemma exists_twistFixed_den (harch : GammaArchimedean ℚᵐ⁰) {γ : ℚᵐ⁰} (hγ0 : 0 < γ) (hγ : γ < 1)
    {f : PowerSeries (Ambient F)} (hf : GSuperEntire γ f)
    {Q : Polynomial (Ambient F)} (hQ : Q.eval (ambTheta F) = 1) (hQ0 : Q ≠ 0)
    (hrel : frobTwist (R := Ambient F) (p := Nat.card F) 1 f * (Q : PowerSeries (Ambient F))
      = f * ((polyTwist (q := Nat.card F) 1 Q : Polynomial (Ambient F)) :
          PowerSeries (Ambient F))) :
    ∃ b h : Polynomial (Ambient F), b ≠ 0 ∧
      (∀ n, b.coeff n ∈ ambF F) ∧ (∀ n, h.coeff n ∈ ambF F) ∧
      f * (b : PowerSeries (Ambient F)) = h * (Q : PowerSeries (Ambient F)) := by
  classical
have hγ1 : γ ≤ 1 := le_of_lt hγ
have hfe : GEntire (K := Ambient F) f :=
  GSuperEntire.entire hγ1 (fun x hx => harch γ hγ x hx) hf
have hQps : (Q : PowerSeries (Ambient F)) ≠ 0 := polynomial_coe_powerSeries_ne_zero.mpr hQ0
have hptQ : (polyTwist (q := Nat.card F) 1 Q : Polynomial (Ambient F)) ≠ 0 := by
  rw [polyTwist, polyTwistHom_apply]
  exact fun h => hQ0 ((Polynomial.map_eq_zero_iff (frobPowHom_injective 1)).mp h)
have hσQ : frobTwist (R := Ambient F) (p := Nat.card F) 1 (Q : PowerSeries (Ambient F)) ≠ 0 := by
  rw [← coe_polyTwist' 1 Q]
  exact fun h => hptQ (Polynomial.coe_injective (Ambient F) (by rw [h, Polynomial.coe_zero]))
have hrel' : frobTwist (R := Ambient F) (p := Nat.card F) 1 f * (Q : PowerSeries (Ambient F))
    = f * frobTwist (R := Ambient F) (p := Nat.card F) 1 (Q : PowerSeries (Ambient F)) := by
  rw [hrel, coe_polyTwist' 1 Q]
-- the potential-denominator ideal
set M := denIdeal f Q with hM
obtain ⟨b₀, hb₀⟩ := (IsPrincipalIdealRing.principal M).principal
have hQmem : Q ∈ M := ⟨f, hfe, rfl⟩
have hMne : M ≠ ⊥ := by
  intro h
  rw [h, Submodule.mem_bot] at hQmem
  exact hQ0 hQmem
have hb0ne : b₀ ≠ 0 := by
  intro h0
  apply hMne
  rw [hb₀, h0]
  exact Submodule.span_singleton_eq_bot.mpr rfl
have hb0mem : b₀ ∈ M := by
  rw [hb₀]; exact Submodule.mem_span_singleton_self b₀
obtain ⟨G, hG, hGb⟩ := hb0mem
have hσb₀ : ((polyTwist (q := Nat.card F) 1 b₀ : Polynomial (Ambient F)) :
    PowerSeries (Ambient F)) = frobTwist (R := Ambient F) (p := Nat.card F) 1
      (b₀ : PowerSeries (Ambient F)) := coe_polyTwist' 1 b₀
-- the twist-stability of `M`
have hsig' : f * ((polyTwist (q := Nat.card F) 1 b₀ : Polynomial (Ambient F)) :
    PowerSeries (Ambient F)) = frobTwist (R := Ambient F) (p := Nat.card F) 1 G
      * (Q : PowerSeries (Ambient F)) := by
  have h1 : frobTwist (R := Ambient F) (p := Nat.card F) 1
      (f * (b₀ : PowerSeries (Ambient F)))
      = frobTwist (R := Ambient F) (p := Nat.card F) 1
        (G * (Q : PowerSeries (Ambient F))) := by rw [hGb]
  rw [frobTwist_mul, frobTwist_mul] at h1
  rw [hσb₀]
  refine mul_right_cancel₀ hσQ ?_
  calc (f * frobTwist (R := Ambient F) (p := Nat.card F) 1 (b₀ : PowerSeries (Ambient F)))
        * frobTwist (R := Ambient F) (p := Nat.card F) 1 (Q : PowerSeries (Ambient F))
      = (f * frobTwist (R := Ambient F) (p := Nat.card F) 1 (Q : PowerSeries (Ambient F)))
        * frobTwist (R := Ambient F) (p := Nat.card F) 1 (b₀ : PowerSeries (Ambient F)) := by
          ring
    _ = (frobTwist (R := Ambient F) (p := Nat.card F) 1 f * (Q : PowerSeries (Ambient F)))
        * frobTwist (R := Ambient F) (p := Nat.card F) 1 (b₀ : PowerSeries (Ambient F)) := by
          rw [congrArg (· * frobTwist (R := Ambient F) (p := Nat.card F) 1
            (b₀ : PowerSeries (Ambient F))) hrel']
    _ = (frobTwist (R := Ambient F) (p := Nat.card F) 1 f
          * frobTwist (R := Ambient F) (p := Nat.card F) 1 (b₀ : PowerSeries (Ambient F)))
        * (Q : PowerSeries (Ambient F)) := by ring
    _ = (frobTwist (R := Ambient F) (p := Nat.card F) 1 G
          * frobTwist (R := Ambient F) (p := Nat.card F) 1 (Q : PowerSeries (Ambient F)))
        * (Q : PowerSeries (Ambient F)) := by
          rw [congrArg (· * (Q : PowerSeries (Ambient F))) h1]
    _ = (frobTwist (R := Ambient F) (p := Nat.card F) 1 G * (Q : PowerSeries (Ambient F)))
        * frobTwist (R := Ambient F) (p := Nat.card F) 1 (Q : PowerSeries (Ambient F)) := by
          ring
have hsig : polyTwist (q := Nat.card F) 1 b₀ ∈ M :=
  ⟨frobTwist (R := Ambient F) (p := Nat.card F) 1 G, hG.frobTwist 1, hsig'⟩
-- `b₀ | σ(b₀)`, and the cofactor is a constant
obtain ⟨c, hc⟩ : ∃ c, polyTwist (q := Nat.card F) 1 b₀ = b₀ * c := by
  have hmem : polyTwist (q := Nat.card F) 1 b₀
      ∈ Ideal.span ({b₀} : Set (Polynomial (Ambient F))) := by
    rw [show Ideal.span ({b₀} : Set (Polynomial (Ambient F))) = M from hb₀.symm]
    exact hsig
  exact Ideal.mem_span_singleton.mp hmem
have hpt0 : polyTwist (q := Nat.card F) 1 b₀ ≠ 0 := by
  rw [polyTwist, polyTwistHom_apply]
  exact fun h => hb0ne ((Polynomial.map_eq_zero_iff (frobPowHom_injective 1)).mp h)
have hc0 : c ≠ 0 := by
  rintro rfl
  rw [mul_zero] at hc
  exact hpt0 hc
have hdegc : c.natDegree = 0 := by
  have h2 : (polyTwist (q := Nat.card F) 1 b₀).natDegree = b₀.natDegree := by
    rw [polyTwist, polyTwistHom_apply]
    exact Polynomial.natDegree_map_eq_of_injective (frobPowHom_injective 1) b₀
  have h1 : (polyTwist (q := Nat.card F) 1 b₀).natDegree = b₀.natDegree + c.natDegree := by
    rw [hc, Polynomial.natDegree_mul hb0ne hc0]
  omega
set d : Ambient F := c.coeff 0 with hd
have hcd : c = Polynomial.C d := by
  rw [hd]; exact Polynomial.eq_C_of_natDegree_eq_zero hdegc
have hcP : polyTwist (q := Nat.card F) 1 b₀ = b₀ * Polynomial.C d := by
  rw [hc, hcd]
have hd0 : d ≠ 0 := by
  rintro h0
  exact hc0 (by rw [hcd, h0, Polynomial.C_0])
have hGb' : f * (b₀ : PowerSeries (Ambient F)) = G * (Q : PowerSeries (Ambient F)) := hGb
-- the witness satisfies `σ(G) = G·d`
have hGC : frobTwist (R := Ambient F) (p := Nat.card F) 1 G = G * PowerSeries.C d := by
  have hkey : frobTwist (R := Ambient F) (p := Nat.card F) 1 G * (Q : PowerSeries (Ambient F))
      = (G * PowerSeries.C d) * (Q : PowerSeries (Ambient F)) := by
    rw [← hsig', hcP, Polynomial.coe_mul, Polynomial.coe_C]
    calc f * ((b₀ : PowerSeries (Ambient F)) * PowerSeries.C d)
        = (f * (b₀ : PowerSeries (Ambient F))) * PowerSeries.C d := by ring
      _ = (G * (Q : PowerSeries (Ambient F))) * PowerSeries.C d := by rw [hGb']
      _ = (G * PowerSeries.C d) * (Q : PowerSeries (Ambient F)) := by ring
  exact mul_right_cancel₀ hQps hkey
by_cases hG0 : G = 0
· have hf0 : f = 0 := by
    have h : f * (b₀ : PowerSeries (Ambient F)) = 0 := by rw [hGb', hG0, zero_mul]
    rcases mul_eq_zero.mp h with h' | h'
    · exact h'
    · exact absurd h' (polynomial_coe_powerSeries_ne_zero.mpr hb0ne)
  exact ⟨1, 0, one_ne_zero,
    (by intro n; rw [Polynomial.coeff_one]; split <;>
        [exact (ambF F).one_mem; exact (ambF F).zero_mem]),
    (by intro n; rw [Polynomial.coeff_zero]; exact (ambF F).zero_mem),
    (by rw [hf0]; simp)⟩
· obtain ⟨n₀, hn₀⟩ : ∃ n, G.coeff n ≠ 0 := by
    by_contra h
    push Not at h
    exact hG0 (PowerSeries.ext h)
  set a : Ambient F := G.coeff n₀ with ha
  have ha0 : a ≠ 0 := hn₀
  have haq : a ^ Nat.card F = a * d := by
    have h1 := congrArg (PowerSeries.coeff n₀) hGC
    rw [frobTwist_coeff, pow_one, PowerSeries.coeff_mul_C] at h1
    exact h1
  have hainv : (a⁻¹) ^ Nat.card F = a⁻¹ * d⁻¹ := by
    rw [inv_pow, haq, mul_inv, mul_comm]
  set H : PowerSeries (Ambient F) := G * PowerSeries.C (a⁻¹) with hHdef
  set b₁ : Polynomial (Ambient F) := b₀ * Polynomial.C (a⁻¹) with hb₁def
  have hb₁ne : b₁ ≠ 0 := by
    rw [hb₁def]
    refine mul_ne_zero hb0ne (Polynomial.C_ne_zero.mpr (inv_ne_zero ha0))
  have hσb₁ : frobTwist (R := Ambient F) (p := Nat.card F) 1 (b₀ : PowerSeries (Ambient F))
      = (b₀ : PowerSeries (Ambient F)) * PowerSeries.C d := by
    rw [← coe_polyTwist' 1 b₀, hcP, Polynomial.coe_mul, Polynomial.coe_C]
  have hdd : d * (a⁻¹ * d⁻¹) = a⁻¹ := by
    rw [← mul_assoc, mul_comm d a⁻¹, mul_assoc, mul_inv_cancel₀ hd0, mul_one]
  have hb₁σ : frobTwist (R := Ambient F) (p := Nat.card F) 1 (b₁ : PowerSeries (Ambient F))
      = (b₁ : PowerSeries (Ambient F)) := by
    rw [hb₁def, Polynomial.coe_mul, Polynomial.coe_C, frobTwist_mul, hσb₁, frobTwist_C, pow_one,
      hainv, mul_assoc, ← PowerSeries.C.map_mul, hdd]
  have hHinv : frobTwist (R := Ambient F) (p := Nat.card F) 1 H = H := by
    rw [hHdef, frobTwist_mul, hGC, frobTwist_C, pow_one, hainv, mul_assoc,
      ← PowerSeries.C.map_mul, hdd]
  have hHent : GEntire (K := Ambient F) H := by
    rw [hHdef]; exact hG.mul (GEntire.C (a⁻¹))
  obtain ⟨p₀, hp₀⟩ := exists_polynomial_of_gEntire_of_frobTwist_one_eq
    (GEntire.polynomial b₁) hb₁σ
  obtain ⟨p₁, hp₁⟩ := exists_polynomial_of_gEntire_of_frobTwist_one_eq hHent hHinv
  -- the equation `f·b₁ = H·Q`
  have hFb₁ : f * (b₁ : PowerSeries (Ambient F)) = H * (Q : PowerSeries (Ambient F)) := by
    rw [hb₁def, Polynomial.coe_mul, Polynomial.coe_C, hHdef]
    calc f * ((b₀ : PowerSeries (Ambient F)) * PowerSeries.C (a⁻¹))
        = (f * (b₀ : PowerSeries (Ambient F))) * PowerSeries.C (a⁻¹) := by ring
      _ = (G * (Q : PowerSeries (Ambient F))) * PowerSeries.C (a⁻¹) := by rw [hGb']
      _ = (G * PowerSeries.C (a⁻¹)) * (Q : PowerSeries (Ambient F)) := by ring
  -- super-entireness of the pieces
  have hb₁se : GSuperEntire γ (b₁ : PowerSeries (Ambient F)) := by
    rw [← hp₀]; exact GSuperEntire.polynomial hγ0 hγ1 _
  have hHse : GSuperEntire γ H := by
    rw [← hp₁]; exact GSuperEntire.polynomial hγ0 hγ1 _
  have hQse : GSuperEntire γ (Q : PowerSeries (Ambient F)) :=
    GSuperEntire.polynomial hγ0 hγ1 Q
  refine ⟨b₁, p₁.map (ambCoeff F), hb₁ne, ?_, ?_, ?_⟩
  · intro n
    have h := coeff_mem_ambF_of_frobTwist_one_eq (F := F) (f := (b₁ : PowerSeries (Ambient F))) hb₁σ n
    simpa only [Polynomial.coeff_coe] using h
  · intro n
    rw [Polynomial.coeff_map]
    exact ambCoeff_mem_ambF F _
  · rw [hFb₁, hp₁]


/-! ## §3. The mechanism of `PLAN.md` §«continued 33»: the shared factor of `Q` and `σ Q` -/

/-- `polyTwist 1` preserves divisibility (it is a ring hom). -/
lemma polyTwist_dvd {a b : Polynomial (Ambient F)} (h : a ∣ b) :
    polyTwist (q := Nat.card F) 1 a ∣ polyTwist (q := Nat.card F) 1 b := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨polyTwist (q := Nat.card F) 1 c, by rw [polyTwist_mul]⟩

/-- ★★ **The mechanism of `PLAN.md` §«continued 33»**: a potential denominator `b` which is
`σ`-invariant up to a nonzero constant divides both `Q` and `σ Q`.  Hence `b ∣ gcd (σ Q) Q`, and the gcd
is a unit only when `b` is a constant — which is `Rationality.lean`'s `hcd`
(`polyTwist 1 b₀ = b₀ * C d`) applied to `hQmem : Q ∈ (b₀)`. -/
lemma dvd_gcd_of_twist_eq_mul {b Q c : Polynomial (Ambient F)} (hbQ : b ∣ Q)
    (hσ : polyTwist (q := Nat.card F) 1 b = b * c) (hc : c ≠ 0) :
    b ∣ Q ∧ b ∣ polyTwist (q := Nat.card F) 1 Q := by
  refine ⟨hbQ, ?_⟩
  obtain ⟨g, hg⟩ := hbQ
  refine ⟨c * polyTwist (q := Nat.card F) 1 g, ?_⟩
  rw [hg, polyTwist_mul, hσ]
  ring

end ZagierHoffmanPositiveChar
