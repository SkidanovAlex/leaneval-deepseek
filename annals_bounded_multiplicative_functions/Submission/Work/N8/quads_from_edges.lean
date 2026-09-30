import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.solve_adi
import Submission.Work.BMF.polyrel_basic
import Submission.Work.BMF.n8_defs
import Submission.Work.BMF.primesIn_card_le_pi0
import Submission.Work.N8.solve_adi_explicit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

open Polynomial Finset
open Work.BMF

set_option maxHeartbeats 3200000

/-- Counting bound for the primes of `S` (all `≥ Y ≥ 1`) that divide `q`:
`#(S ∩ {p : p ∣ q}) · log Y ≤ log q`.  Proof: the product of those primes divides `q`
(they are distinct primes, hence a subset of `q.primeFactors`), and it is at least
`Y ^ #(S ∩ …)`. -/
private theorem card_filter_dvd_mul_log_le' {S : Finset ℕ} {q : ℕ} {Y : ℝ}
    (hS : ∀ p ∈ S, p.Prime) (hY1 : 1 ≤ Y) (hYp : ∀ p ∈ S, Y ≤ (p : ℝ)) (hq : 0 < q) :
    ((S.filter (fun p => p ∣ q)).card : ℝ) * Real.log Y ≤ Real.log (q : ℝ) := by
  classical
  have hsub : S.filter (fun p => p ∣ q) ⊆ q.primeFactors := by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact Nat.mem_primeFactors.mpr ⟨hS p hp.1, hp.2, hq.ne'⟩
  have hdvd : ((S.filter (fun p => p ∣ q)).prod (fun p => p) : ℕ) ∣ q :=
    dvd_trans (Finset.prod_dvd_prod_of_subset _ q.primeFactors (fun p => p) hsub)
      (Nat.prod_primeFactors_dvd q)
  have hle : (((S.filter (fun p => p ∣ q)).prod (fun p => p) : ℕ) : ℝ) ≤ (q : ℝ) :=
    by exact_mod_cast Nat.le_of_dvd hq hdvd
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY1
  have hpow : Y ^ (S.filter (fun p => p ∣ q)).card
      ≤ (((S.filter (fun p => p ∣ q)).prod (fun p => p) : ℕ) : ℝ) := by
    rw [← Finset.prod_const, Nat.cast_prod]
    refine Finset.prod_le_prod₀ (fun p hp => le_trans zero_le_one hY1) (fun p hp => ?_)
    exact hYp p (Finset.mem_filter.mp hp).1
  have hlog := Real.log_le_log (pow_pos hYpos _) (le_trans hpow hle)
  rw [Real.log_pow] at hlog
  exact hlog

/-- **Step 1 of MRTTZ §3: solve each edge (N6) and turn it into good quadruples.**
For every edge `e` of the `ADI`-family (with its approximate dilation invariance data), `solve_adi`
gives a single `T_e`, two lattice polynomials `γ₁, γ₂` and a modulus `q_e`; after deleting from the
certifying prime set the `O(1)` primes dividing `q_e` (leaving `Ps`) and taking `q` to be the
*minimal* natural number with `IntegralOn q γ`, one obtains good quadruples at `e.x₁` and `e.x₂`
with the same `T_e`, plus the relation `IntegralOn 1 (dil p₂ γ₁ - dil p₁ γ₂)`.

The hypotheses are exactly what `solve_adi` needs: `C₀ := max C 10` (so `N*L ≤ C₀*x` and
`x ≤ C₀*(N*L)` come from `IsFam` with `x + L ≤ 10*X`), `N := X/L ≥ 100 C₀⁴`, `C1c k C₀ ≤ δ⁻¹` so
that `solve_adi`'s constant fits in `δ⁻¹`, `Q_e = ∏S_e` huge so that `Z^K ≤ Q_e` with
`Z = a₁a₂p₁p₂NL ≤ (2P₁)^{2ℓ+2} X` and `∏S_e ≥ (P₂/2)^{c π₀(P₂)}`, the `δ`-modulus bound
`K0c k (…)/log(P₂/2) ≤ (c-δ)π₀(P₂)` for the removal of the `ω(q)` primes with `q ≤ Z^{K0c k} ≤ X^{1/δ}`,
and `δ ≤ c` so that the surviving prime set still has `≥ δ π₀(P₂)` elements. -/
theorem quads_from_edges (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ X₀ : ℝ, ∀ (f : ℕ → ℂ) (c C X L P₁ P₂ : ℝ) (ℓ : ℕ)
      (A : Work.BMF.ADIData k f c C X L P₁ P₂ ℓ),
      0 < c → X₀ ≤ X → 10 ≤ C → 2 ≤ L → L ≤ X → 4 ≤ P₂ → δ ≤ c →
      100 * (max C 10) ^ 4 ≤ X / L →
      Work.BMF.C1c k (max C 10) ≤ δ⁻¹ →
      2 * (Work.BMF.K0c k : ℝ) * ((2 * ℓ + 2) * Real.log (2 * P₁) + Real.log X + 1) ≤
        (1 / δ) * Real.log X →
      (Work.BMF.K0c k : ℝ) * ((2 * ℓ + 2) * Real.log (2 * P₁) + Real.log X + 1) /
          Real.log (P₂ / 2) ≤ (c - δ) * Work.BMF.pi0 P₂ →
      ((2 * P₁) ^ (2 * ℓ + 2) * X) ^ (max (Work.BMF.Kc k) 1) ≤
        (P₂ / 2) ^ ⌈c * Work.BMF.pi0 P₂⌉₊ →
      ∀ e ∈ A.edges, ∃ (T : ℝ) (q₁ qf₁ : ℕ) (γ₁ : Polynomial ℝ) (Ps₁ : Finset ℕ)
        (q₂ qf₂ : ℕ) (γ₂ : Polynomial ℝ) (Ps₂ : Finset ℕ),
        Work.BMF.GoodQuad A δ e.x₁ T q₁ qf₁ γ₁ Ps₁ ∧
        Work.BMF.GoodQuad A δ e.x₂ T q₂ qf₂ γ₂ Ps₂ ∧
        Work.BMF.IntegralOn 1 (Work.BMF.dil (e.p₂ : ℝ) γ₁ - Work.BMF.dil (e.p₁ : ℝ) γ₂) := by
  classical
  refine ⟨1, ?_⟩
  intro f c C X L P₁ P₂ ℓ A hc hX hC10 hL2 hLX hP24 hδc hN100 hC1c hK0log hK0card hZKhi e he
  -- ### the constant `C₀ = max C 10` and the scale `N₀ = X/L`
  let C₀ : ℝ := max C 10
  have hC0eq : C₀ = max C 10 := rfl
  have hC0ge : 10 ≤ C₀ := le_max_right C 10
  have hC0pos : 0 < C₀ := lt_of_lt_of_le (by norm_num) hC0ge
  have hC0one : 1 ≤ C₀ := le_trans (by norm_num) hC0ge
  have hCle : C ≤ C₀ := le_max_left C 10
  let N0 : ℝ := X / L
  have hN0eq : N0 = X / L := rfl
  have hLpos : 0 < L := by linarith
  have hXpos : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hX2 : 2 ≤ X := by linarith
  have hP2pos : 0 < P₂ := by linarith
  have hP2half2 : 2 ≤ P₂ / 2 := by linarith
  have hP2half1 : 1 ≤ P₂ / 2 := by linarith
  have hlogP2half : 0 < Real.log (P₂ / 2) := Real.log_pos (by linarith)
  have hN0L : N0 * L = X := by rw [hN0eq]; field_simp
  have hN0pos : 0 < N0 := by rw [hN0eq]; positivity
  -- ### the edge data
  obtain ⟨a₁, b₁, a₂, b₂, S, hSpr, hScard, hb1P1, hb1a1, ha1le, hb2P1, hb2a2, ha2le,
    ha1N, hNa1, ha2N, hNa2, hedge, hpoly1, hpoly2⟩ := A.adi e he
  obtain ⟨hx1fam, hx2fam, hx12, hp12, hp1pi, hp2pi, hgeo⟩ := A.geom e he
  -- ### positivity of the dilation parameters
  have hp1prime : e.p₁.Prime := hp1pi.1
  have hp2prime : e.p₂.Prime := hp2pi.1
  have hp1ge2 : 2 ≤ e.p₁ := hp1prime.two_le
  have hp2ge2 : 2 ≤ e.p₂ := hp2prime.two_le
  have hp1_le_2P1 : (e.p₁ : ℝ) ≤ 2 * P₁ := hp1pi.2.2
  have hp2_le_2P1 : (e.p₂ : ℝ) ≤ 2 * P₁ := hp2pi.2.2
  have hP1one : 1 ≤ P₁ := by
    have h2 : (2 : ℝ) ≤ 2 * P₁ := by
      have h3 : (2 : ℝ) ≤ (e.p₁ : ℝ) := by exact_mod_cast hp1ge2
      linarith
    linarith
  have hP1pos : 0 < P₁ := lt_of_lt_of_le zero_lt_one hP1one
  have hp1_1 : 1 ≤ e.p₁ := by omega
  have hp2_1 : 1 ≤ e.p₂ := by omega
  have hb1_1 : 1 ≤ b₁ := by
    have h : (1 : ℝ) ≤ (b₁ : ℝ) := le_trans (one_le_pow₀ hP1one) hb1P1
    exact_mod_cast h
  have hb2_1 : 1 ≤ b₂ := by
    have h : (1 : ℝ) ≤ (b₂ : ℝ) := le_trans (one_le_pow₀ hP1one) hb2P1
    exact_mod_cast h
  have hdiff1 : (0 : ℝ) ≤ (a₁ : ℝ) - b₁ := by
    have h : (b₁ : ℝ) < (a₁ : ℝ) := by exact_mod_cast hb1a1
    linarith
  have hdiff2 : (0 : ℝ) ≤ (a₂ : ℝ) - b₂ := by
    have h : (b₂ : ℝ) < (a₂ : ℝ) := by exact_mod_cast hb2a2
    linarith
  -- ### the family bounds
  have hx1_lo : X / 10 ≤ e.x₁ := (A.isFam.1 e.x₁ hx1fam).1
  have hx1_hi : e.x₁ + L ≤ 10 * X := (A.isFam.1 e.x₁ hx1fam).2
  have hx2_lo : X / 10 ≤ e.x₂ := (A.isFam.1 e.x₂ hx2fam).1
  have hx2_hi : e.x₂ + L ≤ 10 * X := (A.isFam.1 e.x₂ hx2fam).2
  have hx1a : N0 * L ≤ C₀ * e.x₁ := by
    rw [hN0L]; nlinarith [hx1_lo, hC0ge]
  have hx1b : e.x₁ ≤ C₀ * (N0 * L) := by
    rw [hN0L]; nlinarith [hx1_hi, hLpos, hC0ge]
  have hx2a : N0 * L ≤ C₀ * e.x₂ := by
    rw [hN0L]; nlinarith [hx2_lo, hC0ge]
  have hx2b : e.x₂ ≤ C₀ * (N0 * L) := by
    rw [hN0L]; nlinarith [hx2_hi, hLpos, hC0ge]
  have hN100' : 100 * C₀ ^ 4 ≤ N0 := by rw [hN0eq]; exact hN100
  -- ### the modulus `Q_e = ∏ S`
  let Qe : ℕ := S.prod (fun p => p)
  have hQepos : 0 < Qe := by
    apply Finset.prod_pos
    intro p hp
    exact Nat.Prime.pos (hSpr p hp).1
  have hQeR : (Qe : ℝ) = ∏ p ∈ S, (p : ℝ) := by
    rw [show Qe = S.prod (fun p => p) from rfl]
    exact Nat.cast_prod (fun p => p) S
  -- ### raise the `PolyRel` constants from `C` to `C₀`
  have hrel1 : PolyRel k C₀ (1 / (Qe : ℝ)) (e.x₁ / a₁) (L / a₁) (dil a₁ (A.pol e.x₁))
      (e.x₁ / b₁) (L / b₁) (dil b₁ (A.pol e.x₁)) :=
    PolyRel.mono hpoly1 hCle (by positivity) (by positivity)
  have hrel2 : PolyRel k C₀ (1 / (Qe : ℝ)) (e.x₂ / a₂) (L / a₂) (dil a₂ (A.pol e.x₂))
      (e.x₂ / b₂) (L / b₂) (dil b₂ (A.pol e.x₂)) :=
    PolyRel.mono hpoly2 hCle (by positivity) (by positivity)
  have hedge' : PolyRel k C₀ (1 / (Qe : ℝ)) (e.x₁ / (e.p₂ : ℝ)) (L / (e.p₂ : ℝ))
      (dil (e.p₂ : ℝ) (A.pol e.x₁)) (e.x₂ / (e.p₁ : ℝ)) (L / (e.p₁ : ℝ))
      (dil (e.p₁ : ℝ) (A.pol e.x₂)) :=
    PolyRel.mono hedge hCle (by positivity) (by positivity)
  -- ### `Z ≤ Z₀` and the largeness `Z^{Kc} ≤ Qe`
  let B : ℝ := 2 * P₁
  have hBeq : B = 2 * P₁ := rfl
  let Z : ℝ := (a₁ : ℝ) * (a₂ : ℝ) * (e.p₁ : ℝ) * (e.p₂ : ℝ) * N0 * L
  have hZeq0 : Z = (a₁ : ℝ) * (a₂ : ℝ) * (e.p₁ : ℝ) * (e.p₂ : ℝ) * N0 * L := rfl
  let Z0 : ℝ := B ^ (2 * ℓ + 2) * X
  have hZ0eq : Z0 = B ^ (2 * ℓ + 2) * X := rfl
  have hB1 : 1 ≤ B := by rw [hBeq]; linarith
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB1
  have hZeq : Z = (a₁ : ℝ) * (a₂ : ℝ) * (e.p₁ : ℝ) * (e.p₂ : ℝ) * X := by
    rw [hZeq0, hN0eq]; field_simp
  have ha1pos : (0 : ℝ) < (a₁ : ℝ) := by exact_mod_cast (by omega : 0 < a₁)
  have ha2pos : (0 : ℝ) < (a₂ : ℝ) := by exact_mod_cast (by omega : 0 < a₂)
  have hp1Rpos : (0 : ℝ) < (e.p₁ : ℝ) := by exact_mod_cast hp1prime.pos
  have hp2Rpos : (0 : ℝ) < (e.p₂ : ℝ) := by exact_mod_cast hp2prime.pos
  have hZpos : 0 < Z := by
    rw [hZeq]; positivity
  have hZle : Z ≤ Z0 := by
    rw [hZeq, hZ0eq, hBeq]
    have h12 : (a₁ : ℝ) * (a₂ : ℝ) ≤ ((2 * P₁) ^ ℓ) * ((2 * P₁) ^ ℓ) :=
      mul_le_mul ha1le ha2le (by positivity) (by positivity)
    have h34 : (e.p₁ : ℝ) * (e.p₂ : ℝ) ≤ (2 * P₁) * (2 * P₁) :=
      mul_le_mul hp1_le_2P1 hp2_le_2P1 (by positivity) (by positivity)
    have hstep : (a₁ : ℝ) * (a₂ : ℝ) * (e.p₁ : ℝ) * (e.p₂ : ℝ)
        ≤ ((2 * P₁) ^ ℓ) * ((2 * P₁) ^ ℓ) * (2 * P₁) * (2 * P₁) := by
      calc (a₁ : ℝ) * (a₂ : ℝ) * (e.p₁ : ℝ) * (e.p₂ : ℝ)
          = ((a₁ : ℝ) * (a₂ : ℝ)) * ((e.p₁ : ℝ) * (e.p₂ : ℝ)) := by ring
        _ ≤ (((2 * P₁) ^ ℓ) * ((2 * P₁) ^ ℓ)) * ((2 * P₁) * (2 * P₁)) :=
            mul_le_mul h12 h34 (by positivity) (by positivity)
        _ = ((2 * P₁) ^ ℓ) * ((2 * P₁) ^ ℓ) * (2 * P₁) * (2 * P₁) := by ring
    calc (a₁ : ℝ) * (a₂ : ℝ) * (e.p₁ : ℝ) * (e.p₂ : ℝ) * X
        = ((a₁ : ℝ) * (a₂ : ℝ) * (e.p₁ : ℝ) * (e.p₂ : ℝ)) * X := by ring
      _ ≤ (((2 * P₁) ^ ℓ) * ((2 * P₁) ^ ℓ) * (2 * P₁) * (2 * P₁)) * X :=
          mul_le_mul_of_nonneg_right hstep hXpos.le
      _ = (2 * P₁) ^ (2 * ℓ + 2) * X := by
          have hkey2 : (2 * P₁) ^ ℓ * (2 * P₁) ^ ℓ * (2 * P₁) * (2 * P₁)
              = (2 * P₁) ^ (ℓ + ℓ) * ((2 * P₁) * (2 * P₁)) := by
            rw [← pow_add]; ring
          rw [hkey2, ← pow_two, ← pow_add, show ℓ + ℓ + 2 = 2 * ℓ + 2 by omega]
  have hZ0ge1 : 1 ≤ Z0 := by
    rw [hZ0eq, hBeq]
    have h := mul_le_mul (one_le_pow₀ (by linarith : (1 : ℝ) ≤ 2 * P₁)) hX1
      (by norm_num) (by positivity : (0 : ℝ) ≤ (2 * P₁) ^ (2 * ℓ + 2))
    simpa using h
  have hZ0pos : 0 < Z0 := lt_of_lt_of_le zero_lt_one hZ0ge1
  -- `(P₂/2)^{⌈cπ₀⌉₊} ≤ Qe`
  have hceil : ⌈c * pi0 P₂⌉₊ ≤ S.card := by
    rw [Nat.ceil_le]; exact hScard
  have hQe_ge : (P₂ / 2) ^ ⌈c * pi0 P₂⌉₊ ≤ (Qe : ℝ) := by
    rw [hQeR]
    refine le_trans (pow_le_pow_right₀ hP2half1 hceil) ?_
    calc (P₂ / 2) ^ S.card = ∏ _p ∈ S, (P₂ / 2) := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ S, (p : ℝ) :=
          Finset.prod_le_prod₀ (fun p hp => by positivity) (fun p hp => (hSpr p hp).2.1)
  have hZK : Z ^ Kc k ≤ (Qe : ℝ) := by
    have h1 : Z ^ Kc k ≤ Z0 ^ (max (Kc k) 1) := by
      have := pow_le_pow_left₀ (le_of_lt hZpos) hZle (Kc k)
      refine le_trans this ?_
      exact pow_le_pow_right₀ hZ0ge1 (le_max_left (Kc k) 1)
    have h2 : Z0 ^ (max (Kc k) 1) ≤ (Qe : ℝ) := by
      rw [hZ0eq, hBeq]
      exact le_trans hZKhi hQe_ge
    exact le_trans h1 h2
  -- ### call N6 with explicit constants
  have ha1N' : (a₁ : ℝ) ≤ C₀ * N0 * ((a₁ : ℝ) - b₁) := by
    calc (a₁ : ℝ) ≤ C * N0 * ((a₁ : ℝ) - b₁) := ha1N
      _ ≤ C₀ * N0 * ((a₁ : ℝ) - b₁) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCle hN0pos.le) hdiff1
  have hNa1' : N0 * ((a₁ : ℝ) - b₁) ≤ C₀ * a₁ := by
    calc N0 * ((a₁ : ℝ) - b₁) ≤ C * (a₁ : ℝ) := hNa1
      _ ≤ C₀ * (a₁ : ℝ) := mul_le_mul_of_nonneg_right hCle (by positivity)
  have ha2N' : (a₂ : ℝ) ≤ C₀ * N0 * ((a₂ : ℝ) - b₂) := by
    calc (a₂ : ℝ) ≤ C * N0 * ((a₂ : ℝ) - b₂) := ha2N
      _ ≤ C₀ * N0 * ((a₂ : ℝ) - b₂) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCle hN0pos.le) hdiff2
  have hNa2' : N0 * ((a₂ : ℝ) - b₂) ≤ C₀ * a₂ := by
    calc N0 * ((a₂ : ℝ) - b₂) ≤ C * (a₂ : ℝ) := hNa2
      _ ≤ C₀ * (a₂ : ℝ) := mul_le_mul_of_nonneg_right hCle (by positivity)
  obtain ⟨T, hT, qe, hqe1, hqeZ, γ₁, γ₂, hγ₁deg, hγ₂deg, hγ₁int, hγ₂int, hε₁, hε₂, hrel⟩ :=
    solve_adi_Kc k C₀ hC0one (A.pol e.x₁) (A.pol e.x₂) e.x₁ e.x₂ L N0
      a₁ b₁ a₂ b₂ e.p₁ e.p₂ Qe
      (A.deg e.x₁ hx1fam) (A.deg e.x₂ hx2fam) hL2 hN100' hx1a hx1b hx2a hx2b
      hp1_1 hp2_1 hb1_1 hb1a1 hb2_1 hb2a2 ha1N' hNa1' ha2N' hNa2' hZK hrel1 hrel2 hedge'
  -- ### `Z^{K₀} ≤ X^{1/δ}` (the log bound)
  have hlogZ0 : Real.log Z0 = (2 * (ℓ : ℝ) + 2) * Real.log (2 * P₁) + Real.log X := by
    rw [hZ0eq, hBeq, Real.log_mul (by positivity) (ne_of_gt hXpos), Real.log_pow]
    push_cast
    ring
  have hK0le : (K0c k : ℝ) * ((2 * (ℓ : ℝ) + 2) * Real.log (2 * P₁) + Real.log X)
      ≤ (1 / (2 * δ)) * Real.log X := by
    have h1 : (K0c k : ℝ) * ((2 * (ℓ : ℝ) + 2) * Real.log (2 * P₁) + Real.log X + 1)
        ≤ (1 / (2 * δ)) * Real.log X := by
      have hkey : (1 / δ) * Real.log X = 2 * ((1 / (2 * δ)) * Real.log X) := by
        field_simp
      rw [hkey] at hK0log
      linarith
    have h2 : (K0c k : ℝ) * ((2 * (ℓ : ℝ) + 2) * Real.log (2 * P₁) + Real.log X)
        ≤ (K0c k : ℝ) * ((2 * (ℓ : ℝ) + 2) * Real.log (2 * P₁) + Real.log X + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith [h1, h2]
  have hZ0pow : Z0 ^ (K0c k) ≤ X ^ (1 / δ) := by
    rw [← Real.log_le_log_iff (pow_pos hZ0pos _) (Real.rpow_pos_of_pos hXpos _)]
    rw [Real.log_pow, hlogZ0, Real.log_rpow hXpos]
    refine le_trans hK0le ?_
    have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX1
    have h2d : 1 / (2 * δ) ≤ 1 / δ := by
      rw [one_div, one_div]
      exact inv_anti₀ hδ (by linarith)
    exact mul_le_mul_of_nonneg_right h2d hlogX
  have hZpow_le : Z ^ (K0c k) ≤ X ^ (1 / δ) :=
    le_trans (pow_le_pow_left₀ (le_of_lt hZpos) hZle (K0c k)) hZ0pow
  have hqe_le_X : (qe : ℝ) ≤ X ^ (1 / δ) := le_trans hqeZ hZpow_le
  -- ### minimal modulus for `γ₁`
  have hQne : (Qe : ℝ) ≠ 0 := by exact_mod_cast hQepos.ne'
  have hqe_int1 : IntegralOn (qe : ℝ) γ₁ := by
    have h1 := hγ₁int.int_mul (Qe : ℤ)
    have h2 : ((Qe : ℤ) : ℝ) * ((qe : ℝ) / (Qe : ℝ)) = (qe : ℝ) := by
      rw [Int.cast_natCast]; field_simp
    rwa [h2] at h1
  have hex1 : ∃ r : ℕ, 1 ≤ r ∧ IntegralOn (r : ℝ) γ₁ := ⟨qe, hqe1, hqe_int1⟩
  set q₁ : ℕ := Nat.find hex1 with hq₁def
  have hq₁1 : 1 ≤ q₁ := by rw [hq₁def]; exact (Nat.find_spec hex1).1
  have hq₁int : IntegralOn (q₁ : ℝ) γ₁ := by rw [hq₁def]; exact (Nat.find_spec hex1).2
  have hq₁min : ∀ r : ℕ, 1 ≤ r → IntegralOn (r : ℝ) γ₁ → q₁ ≤ r := by
    intro r hr hrint
    rw [hq₁def]
    exact Nat.find_min' hex1 ⟨hr, hrint⟩
  have hq₁qe : q₁ ≤ qe := hq₁min qe hqe1 hqe_int1
  have hq₁_le_X : (q₁ : ℝ) ≤ X ^ (1 / δ) :=
    le_trans (by exact_mod_cast hq₁qe) hqe_le_X
  -- ### remove from `S` the primes dividing `q₁`
  set Ps₁ : Finset ℕ := S.filter (fun p => ¬ p ∣ q₁) with hPs₁def
  set R₁ : Finset ℕ := S.filter (fun p => p ∣ q₁) with hR₁def
  have hRcount : ((R₁.card : ℕ) : ℝ) ≤ (c - δ) * pi0 P₂ := by
    have hq1pos : (0 : ℝ) < (q₁ : ℝ) := by exact_mod_cast hq₁1
    have hcard_le := card_filter_dvd_mul_log_le' (S := S) (q := q₁) (Y := P₂ / 2)
      (fun p hp => (hSpr p hp).1) hP2half1 (fun p hp => (hSpr p hp).2.1) (by exact_mod_cast hq₁1)
    rw [← hR₁def] at hcard_le
    have hlogq1 : Real.log (q₁ : ℝ) ≤
        (K0c k : ℝ) * ((2 * (ℓ : ℝ) + 2) * Real.log (2 * P₁) + Real.log X) := by
      have h1 : Real.log (q₁ : ℝ) ≤ (K0c k : ℝ) * Real.log Z := by
        calc Real.log (q₁ : ℝ) ≤ Real.log (Z ^ (K0c k)) := by
              refine Real.log_le_log hq1pos ?_
              exact le_trans (by exact_mod_cast hq₁qe) hqeZ
          _ = (K0c k : ℝ) * Real.log Z := Real.log_pow Z (K0c k)
      have h2 : Real.log Z ≤ (2 * (ℓ : ℝ) + 2) * Real.log (2 * P₁) + Real.log X := by
        rw [← hlogZ0]
        exact Real.log_le_log hZpos hZle
      exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (by positivity))
    have hmain : ((R₁.card : ℕ) : ℝ) * Real.log (P₂ / 2) ≤
        (K0c k : ℝ) * ((2 * (ℓ : ℝ) + 2) * Real.log (2 * P₁) + Real.log X) :=
      le_trans hcard_le hlogq1
    have hdiv : ((K0c k : ℝ) * ((2 * (ℓ : ℝ) + 2) * Real.log (2 * P₁) + Real.log X))
          / Real.log (P₂ / 2) ≤ (c - δ) * pi0 P₂ := by
      refine le_trans (div_le_div_of_nonneg_right ?_ (le_of_lt hlogP2half)) hK0card
      nlinarith [show (0 : ℝ) ≤ (K0c k : ℝ) by positivity]
    have h2 : ((R₁.card : ℕ) : ℝ) * Real.log (P₂ / 2) ≤ ((c - δ) * pi0 P₂) * Real.log (P₂ / 2) := by
      refine le_trans hmain ?_
      rw [div_le_iff₀ hlogP2half] at hdiv
      exact hdiv
    exact le_of_mul_le_mul_right h2 hlogP2half
  have hcard : δ * pi0 P₂ ≤ ((Ps₁.card : ℕ) : ℝ) := by
    have hsplit : (R₁.card : ℝ) + (Ps₁.card : ℝ) = (S.card : ℝ) := by
      have h := Finset.card_filter_add_card_filter_not (s := S) (p := fun p => p ∣ q₁)
      rw [← hR₁def, ← hPs₁def] at h
      rw [← h]; push_cast; ring
    have h1 : δ * pi0 P₂ + (R₁.card : ℝ) ≤ (S.card : ℝ) := by linarith [hRcount, hScard]
    linarith [h1, hsplit]
  -- ### the fine lattice condition on `Ps₁`
  have hMpos1 : 0 < (R₁.prod (fun p => p) : ℕ) := by
    apply Finset.prod_pos
    intro p hp
    have hp' : p ∈ R₁ := hp
    rw [hR₁def] at hp'
    exact Nat.Prime.pos (hSpr p (Finset.mem_filter.mp hp').1).1
  have hQe_fac1 : (Qe : ℝ) = (((R₁.prod (fun p => p) : ℕ) : ℝ)) * Qprod Ps₁ := by
    have h := Finset.prod_filter_mul_prod_filter_not (s := S) (p := fun p => p ∣ q₁)
      (f := fun p => (p : ℝ))
    rw [← hR₁def, ← hPs₁def] at h
    rw [hQeR, ← h, Nat.cast_prod]
    rfl
  have hQpos1 : 0 < Qprod Ps₁ := by
    rw [show Qprod Ps₁ = ∏ p ∈ Ps₁, (p : ℝ) from rfl]
    apply Finset.prod_pos
    intro p hp
    have hp' : p ∈ Ps₁ := hp
    rw [hPs₁def] at hp'
    exact_mod_cast Nat.Prime.pos (hSpr p (Finset.mem_filter.mp hp').1).1
  have hint_fine1 : IntegralOn ((qe : ℝ) / Qprod Ps₁) γ₁ := by
    have h1 := hγ₁int.int_mul (((R₁.prod (fun p => p) : ℕ) : ℤ))
    have h2 : (((R₁.prod (fun p => p) : ℕ) : ℤ) : ℝ) * ((qe : ℝ) / (Qe : ℝ)) = (qe : ℝ) / Qprod Ps₁ := by
      rw [Int.cast_natCast, hQe_fac1]
      field_simp
    rwa [h2] at h1
  -- ### assemble the first good quadruple
  have hTbound : |T| ≤ δ⁻¹ * (X / L) ^ (k + 1) := by
    refine le_trans hT ?_
    rw [hN0eq]
    exact mul_le_mul_of_nonneg_right hC1c (by positivity)
  have hdecomp1 : ∀ t ∈ Set.Icc e.x₁ (e.x₁ + L),
      |deriv (fun s ↦ (A.pol e.x₁).eval s - T / (2 * Real.pi) * Real.log s - γ₁.eval s) t|
        ≤ δ⁻¹ / L := by
    intro t ht
    refine le_trans (hε₁ t ht) ?_
    exact div_le_div_of_nonneg_right hC1c hLpos.le
  have hGQ1 : GoodQuad A δ e.x₁ T q₁ qe γ₁ Ps₁ := by
    refine ⟨hx1fam, hγ₁deg, hTbound, hq₁1, hq₁_le_X, hqe1, hqe_le_X, ?_, hcard, ?_, hq₁int,
      hq₁min, hint_fine1, hdecomp1⟩
    · intro p hp
      exact hSpr p (Finset.mem_filter.mp hp).1
    · intro p hp
      exact (Finset.mem_filter.mp hp).2
  -- ### the same for the second endpoint
  have hqe_int2 : IntegralOn (qe : ℝ) γ₂ := by
    have h1 := hγ₂int.int_mul (Qe : ℤ)
    have h2 : ((Qe : ℤ) : ℝ) * ((qe : ℝ) / (Qe : ℝ)) = (qe : ℝ) := by
      rw [Int.cast_natCast]; field_simp
    rwa [h2] at h1
  have hex2 : ∃ r : ℕ, 1 ≤ r ∧ IntegralOn (r : ℝ) γ₂ := ⟨qe, hqe1, hqe_int2⟩
  set q₂ : ℕ := Nat.find hex2 with hq₂def
  have hq₂1 : 1 ≤ q₂ := by rw [hq₂def]; exact (Nat.find_spec hex2).1
  have hq₂int : IntegralOn (q₂ : ℝ) γ₂ := by rw [hq₂def]; exact (Nat.find_spec hex2).2
  have hq₂min : ∀ r : ℕ, 1 ≤ r → IntegralOn (r : ℝ) γ₂ → q₂ ≤ r := by
    intro r hr hrint
    rw [hq₂def]
    exact Nat.find_min' hex2 ⟨hr, hrint⟩
  have hq₂qe : q₂ ≤ qe := hq₂min qe hqe1 hqe_int2
  have hq₂_le_X : (q₂ : ℝ) ≤ X ^ (1 / δ) :=
    le_trans (by exact_mod_cast hq₂qe) hqe_le_X
  set Ps₂ : Finset ℕ := S.filter (fun p => ¬ p ∣ q₂) with hPs₂def
  set R₂ : Finset ℕ := S.filter (fun p => p ∣ q₂) with hR₂def
  have hRcount2 : ((R₂.card : ℕ) : ℝ) ≤ (c - δ) * pi0 P₂ := by
    have hq2pos : (0 : ℝ) < (q₂ : ℝ) := by exact_mod_cast hq₂1
    have hcard_le := card_filter_dvd_mul_log_le' (S := S) (q := q₂) (Y := P₂ / 2)
      (fun p hp => (hSpr p hp).1) hP2half1 (fun p hp => (hSpr p hp).2.1) (by exact_mod_cast hq₂1)
    rw [← hR₂def] at hcard_le
    have hlogq2 : Real.log (q₂ : ℝ) ≤
        (K0c k : ℝ) * ((2 * (ℓ : ℝ) + 2) * Real.log (2 * P₁) + Real.log X) := by
      have h1 : Real.log (q₂ : ℝ) ≤ (K0c k : ℝ) * Real.log Z := by
        calc Real.log (q₂ : ℝ) ≤ Real.log (Z ^ (K0c k)) := by
              refine Real.log_le_log hq2pos ?_
              exact le_trans (by exact_mod_cast hq₂qe) hqeZ
          _ = (K0c k : ℝ) * Real.log Z := Real.log_pow Z (K0c k)
      have h2 : Real.log Z ≤ (2 * (ℓ : ℝ) + 2) * Real.log (2 * P₁) + Real.log X := by
        rw [← hlogZ0]
        exact Real.log_le_log hZpos hZle
      exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (by positivity))
    have hmain : ((R₂.card : ℕ) : ℝ) * Real.log (P₂ / 2) ≤
        (K0c k : ℝ) * ((2 * (ℓ : ℝ) + 2) * Real.log (2 * P₁) + Real.log X) :=
      le_trans hcard_le hlogq2
    have hdiv : ((K0c k : ℝ) * ((2 * (ℓ : ℝ) + 2) * Real.log (2 * P₁) + Real.log X))
          / Real.log (P₂ / 2) ≤ (c - δ) * pi0 P₂ := by
      refine le_trans (div_le_div_of_nonneg_right ?_ (le_of_lt hlogP2half)) hK0card
      nlinarith [show (0 : ℝ) ≤ (K0c k : ℝ) by positivity]
    have h2 : ((R₂.card : ℕ) : ℝ) * Real.log (P₂ / 2) ≤ ((c - δ) * pi0 P₂) * Real.log (P₂ / 2) := by
      refine le_trans hmain ?_
      rw [div_le_iff₀ hlogP2half] at hdiv
      exact hdiv
    exact le_of_mul_le_mul_right h2 hlogP2half
  have hcard2 : δ * pi0 P₂ ≤ ((Ps₂.card : ℕ) : ℝ) := by
    have hsplit : (R₂.card : ℝ) + (Ps₂.card : ℝ) = (S.card : ℝ) := by
      have h := Finset.card_filter_add_card_filter_not (s := S) (p := fun p => p ∣ q₂)
      rw [← hR₂def, ← hPs₂def] at h
      rw [← h]; push_cast; ring
    have h1 : δ * pi0 P₂ + (R₂.card : ℝ) ≤ (S.card : ℝ) := by linarith [hRcount2, hScard]
    linarith [h1, hsplit]
  have hMpos2 : 0 < (R₂.prod (fun p => p) : ℕ) := by
    apply Finset.prod_pos
    intro p hp
    have hp' : p ∈ R₂ := hp
    rw [hR₂def] at hp'
    exact Nat.Prime.pos (hSpr p (Finset.mem_filter.mp hp').1).1
  have hQe_fac2 : (Qe : ℝ) = (((R₂.prod (fun p => p) : ℕ) : ℝ)) * Qprod Ps₂ := by
    have h := Finset.prod_filter_mul_prod_filter_not (s := S) (p := fun p => p ∣ q₂)
      (f := fun p => (p : ℝ))
    rw [← hR₂def, ← hPs₂def] at h
    rw [hQeR, ← h, Nat.cast_prod]
    rfl
  have hQpos2 : 0 < Qprod Ps₂ := by
    rw [show Qprod Ps₂ = ∏ p ∈ Ps₂, (p : ℝ) from rfl]
    apply Finset.prod_pos
    intro p hp
    have hp' : p ∈ Ps₂ := hp
    rw [hPs₂def] at hp'
    exact_mod_cast Nat.Prime.pos (hSpr p (Finset.mem_filter.mp hp').1).1
  have hint_fine2 : IntegralOn ((qe : ℝ) / Qprod Ps₂) γ₂ := by
    have h1 := hγ₂int.int_mul (((R₂.prod (fun p => p) : ℕ) : ℤ))
    have h2 : (((R₂.prod (fun p => p) : ℕ) : ℤ) : ℝ) * ((qe : ℝ) / (Qe : ℝ)) = (qe : ℝ) / Qprod Ps₂ := by
      rw [Int.cast_natCast, hQe_fac2]
      field_simp
    rwa [h2] at h1
  have hdecomp2 : ∀ t ∈ Set.Icc e.x₂ (e.x₂ + L),
      |deriv (fun s ↦ (A.pol e.x₂).eval s - T / (2 * Real.pi) * Real.log s - γ₂.eval s) t|
        ≤ δ⁻¹ / L := by
    intro t ht
    refine le_trans (hε₂ t ht) ?_
    exact div_le_div_of_nonneg_right hC1c hLpos.le
  have hGQ2 : GoodQuad A δ e.x₂ T q₂ qe γ₂ Ps₂ := by
    refine ⟨hx2fam, hγ₂deg, hTbound, hq₂1, hq₂_le_X, hqe1, hqe_le_X, ?_, hcard2, ?_, hq₂int,
      hq₂min, hint_fine2, hdecomp2⟩
    · intro p hp
      exact hSpr p (Finset.mem_filter.mp hp).1
    · intro p hp
      exact (Finset.mem_filter.mp hp).2
  exact ⟨T, q₁, qe, γ₁, Ps₁, q₂, qe, γ₂, Ps₂, hGQ1, hGQ2, hrel⟩

end Work.N8
