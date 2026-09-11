import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.SelCore
import Submission.Deep
import Submission.Multi
import Submission.MultiMass

/-!
# TASK (child): prove `Submission.Multi.mass_mul_cost_eq` below; it must have a complete proof.
Definitions in Submission/Multi.lean (namespace Submission.Multi; all compile):
  subM T Z := ∀ x, T x ≤ Z x ;  subMM Z T x := Z x - T x (truncated, = Z x − T x when T ≤ Z);
  mass M μ m := (Nat.factorial M : ℝ) * ∏ x, μ x ^ m x / Nat.factorial (m x);
  wCost c μ m := ∏ x, (c * μ x) ^ m x / Nat.factorial (m x);
  sizeM m := ∑ x, m x.
Use Real.exp = 1's Euler constant only in later files; here `c : ℝ` is arbitrary (≥ 0).
## THEOREM
lemma mass_mul_cost_eq {X : Type*} [Fintype X] (μ : X → ℝ) (Z T : X → ℕ) (M t : ℕ)
    (c : ℝ) (hZT : subM T Z) (hZ : sizeM Z = M + t) (hT : sizeM T = t) :
    mass (X := X) M μ (subMM Z T) * wCost c μ T =
      mass (X := X) (M + t) μ Z * ((Nat.factorial M : ℝ) * (Nat.factorial (M + t) : ℝ)⁻¹) *
        c ^ t * (∏ x : X, (Z x).choose (T x) : ℝ) := by ...
(= mass of W := Z∖T of size M, times the cost of T = mass of Z (size M+t) times
 (M!/(M+t)!) · c^t · ∏_x C(Z x, T x).  All reals; factorials are nonzero (Nat.factorial_pos).)
## PROOF OUTLINE
1. W := subMM Z T; when hZT : T ≤ Z pointwise, subMM Z T x = Z x − T x (Nat.sub_eq_of_le-style:
   show subMM Z T = fun x => Z x - T x is by rfl; then use Nat.sub_eq? no: for each x, with
   hZT x : T x ≤ Z x, (Z x − T x) = Z x − T x trivially; so W x = Z x - T x).
2. Unfold mass and wCost; cancel the common ∏_x μ x ^ (Z x − T x) / (Z x − T x)! factors:
   Work out, for each x separately (use `conv`/`ring`/`field_simp` inside ∏ via Finset.prod_congr),
   the real equality:
     μ x ^ (Z x − T x) / (Z x - T x)! * ((c * μ x) ^ T x / (T x)!) * (T x)! / μ x ^ (Z x − T x) * ...
   Cleaner: PROVE the whole thing by pushing through real algebra:
     mass M μ W = M! · ∏_x μ^{Zx−Tx}/(Zx−Tx)!
     mass (M+t) μ Z · (M!·(M+t)!⁻¹) · c^t · ∏ (C(Zx,Tx):ℝ)
                = (M+t)!·∏ μ^{Zx}/Zx! · M!·(M+t)!⁻¹ · c^t · ∏ (Zx!/(Tx!(Zx−Tx)!))-as-choose
     so mass(M+t)μZ·(M!(M+t)!⁻¹)·c^t·∏C(Zx,Tx)
                = M!·∏ μ^{Zx}/Zx! · c^t · ∏ (Zx.choose Tx : ℝ)
     and wCost c μ T = ∏ (cμ)^{Tx}/Tx! = c^t · ∏ μ^{Tx}/Tx!   [c^t = ∏ c^{Tx} over the finite
     type: ∏ x, c ^ T x = c ^ (sizeM T) = c^t — use Finset.prod_pow_eq_pow_sum with hT]
     hence mass M μ W * wCost c μ T
        = M!·∏ [μ^{Zx−Tx}/(Zx−Tx)! · μ^{Tx}/Tx!] · c^t
        = M!·∏ [μ^{Zx}·(1/((Zx−Tx)!Tx!))]·c^t
     and RHS = M!·∏ [μ^{Zx}/Zx! · (Zx.choose Tx : ℝ)]·c^t
     it remains: per x: 1/((Zx−Tx)!·Tx!) = (Zx.choose Tx : ℝ)/Zx!:
        (Zx.choose Tx : ℝ) = (Zx! : ℝ)/((Tx)!·(Zx−Tx)!)  [use Nat.choose_mul_factorial_mul_factorial:
         Zx.choose Tx * (Zx−Tx)! * Tx! = Zx!  — search Mathlib for
         `Nat.choose_mul_factorial_mul_factorial`, or prove it by field_simp + the definitional
         formula (Nat.choose = Zx!/(Tx!·(Zx−Tx)!) via Nat.div exactness — easiest: use the lemma
         `Nat.choose_eq_factorial_div_factorial` hmm not present; derive: by the standard theorem
         `Nat.choose_mul_factorial_mul_factorial (Z x) (T x) :
            (Z x).choose (T x) * (T x)! * (Z x - T x)! = (Z x)!` if it exists in this Mathlib
         (search `#check Nat.choose_mul_factorial_mul_factorial`); if missing, prove
         `(Z x).choose (T x) * (Z x - T x)! = (Z x)! / (T x)!` via Nat.choose_rec / or via
         the recursion of choose, or cast to ℝ and use Nat.factorial division arguments:
         C(Z,T) = Z!/(T!(Z−T)!) as ℕ division exactness: prove by omega-free arithmetic with
         `Nat.choose`-definitional recursion is painful: RECOMMEND: prove the per-coordinate real
         identity `((Z x).choose (T x) : ℝ) * ((T x)! : ℝ) * ((Z x - T x)! : ℝ) = (Z x)! : ℝ`
         by `norm_num`-free induction-free method: use the Mathlib lemma (search) :
         `#check Nat.factorial_mul_choose` / `#check Nat.choose_mul_factorial` /
         `#check Nat.choose_eq_factorial_div_factorial` — pick whatever exists; otherwise prove by
         induction on (Z x) with cases on T x ≤ Z x.  Then `field_simp` with factorial positivity.]
3. Finset-level: use Finset.prod_mul_distrib / Finset.prod_div_distrib and per-coordinate congr
   (`apply Finset.prod_congr rfl; intro x hx; ...`).  Ensure the left ∏ of the RHS expression
   (Zx.choose Tx : ℝ) is handled as a real product.  Provide helper:
     lemma prod_pow_eq_pow_sum' (T : X → ℕ) (c : ℝ) : (∏ x, c ^ T x) = c ^ sizeM T
       [Finset.prod_pow_eq_pow_sum univ T c — #check Finset.prod_pow_eq_pow_sum]
4. Corollaries to also prove (used later; small):
   lemma wCost_mul_mass_le {μ : X → ℝ} {Z T : X → ℕ} {M t : ℕ} (c : ℝ)
       (hZT : subM T Z) (hZ : sizeM Z = M + t) (hT : sizeM T = t)
       (hμ0 : ∀ x, 0 ≤ μ x) (hc0 : 0 ≤ c) :
       mass M μ (subMM Z T) * wCost c μ T ≤
         mass (M + t) μ Z * ((Nat.factorial M : ℝ) * (Nat.factorial (M + t) : ℝ)⁻¹) *
           c ^ t * (∏ x : X, (Z x).choose (T x) : ℝ)
     [= by mass_mul_cost_eq — exact]
   lemma wCost_nonneg (c : ℝ) (hc0 : 0 ≤ c) {μ : X → ℝ} (hμ0 : ∀ x, 0 ≤ μ x) (m : X → ℕ) :
       0 ≤ wCost c μ m   [unfold wCost; prod_nonneg; positivity]
Keep imports as they are.  Namespace Submission.Multi.  No sorries at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
open Classical
open MeasureTheory ProbabilityTheory Measure unitInterval Finset
open scoped NNReal ENNReal BigOperators

namespace Submission

open _root_.SupremumOfSelectorProcesses

namespace Multi

variable {X : Type*} [Fintype X]

/-- coordinate identity for the LHS: μ^{Z−T}/(Z−T)! · (cμ)^{T}/T! = μ^Z c^T/((Z−T)!·T!) -/
lemma coord_prod (μ c : ℝ) (Zx Tx : ℕ) (h : Tx ≤ Zx) :
    μ ^ (Zx - Tx) / (Nat.factorial (Zx - Tx) : ℝ) *
        ((c * μ) ^ Tx / (Nat.factorial Tx : ℝ))
      = μ ^ Zx * c ^ Tx / ((Nat.factorial (Zx - Tx) : ℝ) * (Nat.factorial Tx : ℝ)) := by
  calc
    μ ^ (Zx - Tx) / (Nat.factorial (Zx - Tx) : ℝ) * ((c * μ) ^ Tx / (Nat.factorial Tx : ℝ))
        = (μ ^ (Zx - Tx) * (c * μ) ^ Tx) / ((Nat.factorial (Zx - Tx) : ℝ) * (Nat.factorial Tx : ℝ)) := by
            rw [div_mul_div_comm]
    _ = (μ ^ (Zx - Tx) * (c ^ Tx * μ ^ Tx)) / ((Nat.factorial (Zx - Tx) : ℝ) * (Nat.factorial Tx : ℝ)) := by
            rw [mul_pow]
    _ = (μ ^ (Zx - Tx) * μ ^ Tx * c ^ Tx) / ((Nat.factorial (Zx - Tx) : ℝ) * (Nat.factorial Tx : ℝ)) := by
            ring_nf
    _ = (μ ^ ((Zx - Tx) + Tx) * c ^ Tx) / ((Nat.factorial (Zx - Tx) : ℝ) * (Nat.factorial Tx : ℝ)) := by
            rw [← pow_add]
    _ = μ ^ Zx * c ^ Tx / ((Nat.factorial (Zx - Tx) : ℝ) * (Nat.factorial Tx : ℝ)) := by
            rw [Nat.sub_add_cancel h]

/-- real binomial-coefficient division identity: (Zx.choose Tx)/Zx! = 1/((Zx−Tx)!·Tx!) -/
lemma choose_div_fact (Zx Tx : ℕ) (h : Tx ≤ Zx) :
    (Zx.choose Tx : ℝ) / (Nat.factorial Zx : ℝ)
      = 1 / ((Nat.factorial (Zx - Tx) : ℝ) * (Nat.factorial Tx : ℝ)) := by
  have hfacZ : (Nat.factorial Zx : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero Zx)
  have hfacW : (Nat.factorial (Zx - Tx) : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero (Zx - Tx))
  have hfacT : (Nat.factorial Tx : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero Tx)
  have hchoose : (Zx.choose Tx : ℝ) * (Nat.factorial Tx : ℝ) * (Nat.factorial (Zx - Tx) : ℝ) = (Nat.factorial Zx : ℝ) := by
    exact_mod_cast (Nat.choose_mul_factorial_mul_factorial h)
  field_simp [hfacZ, hfacW, hfacT]
  ring_nf at hchoose ⊢
  exact hchoose

/-- coordinate identity for the RHS: μ^Z/Z! · (Z.choose T : ℝ) · c^T = μ^Z c^T/((Z−T)!·T!) -/
lemma coord_choose (μ c : ℝ) (Zx Tx : ℕ) (h : Tx ≤ Zx) :
    (μ ^ Zx / (Nat.factorial Zx : ℝ)) * (Zx.choose Tx : ℝ) * c ^ Tx
      = μ ^ Zx * c ^ Tx / ((Nat.factorial (Zx - Tx) : ℝ) * (Nat.factorial Tx : ℝ)) := by
  calc
    (μ ^ Zx / (Nat.factorial Zx : ℝ)) * (Zx.choose Tx : ℝ) * c ^ Tx
        = (μ ^ Zx * c ^ Tx) * ((Zx.choose Tx : ℝ) / (Nat.factorial Zx : ℝ)) := by ring
    _ = (μ ^ Zx * c ^ Tx) * (1 / ((Nat.factorial (Zx - Tx) : ℝ) * (Nat.factorial Tx : ℝ))) := by
            rw [choose_div_fact Zx Tx h]
    _ = μ ^ Zx * c ^ Tx / ((Nat.factorial (Zx - Tx) : ℝ) * (Nat.factorial Tx : ℝ)) := by ring

lemma mass_mul_cost_eq {X : Type*} [Fintype X] (μ : X → ℝ) (Z T : X → ℕ) (M t : ℕ)
    (c : ℝ) (hZT : subM T Z) (hZ : sizeM Z = M + t) (hT : sizeM T = t) :
    mass (X := X) M μ (subMM Z T) * wCost c μ T =
      mass (X := X) (M + t) μ Z * ((Nat.factorial M : ℝ) * (Nat.factorial (M + t) : ℝ)⁻¹) *
        c ^ t * (∏ x : X, (Z x).choose (T x) : ℝ) := by
  classical
  have hprodT : (∏ x : X, c ^ T x) = c ^ t := by
    rw [Finset.prod_pow_eq_pow_sum]
    change c ^ sizeM T = c ^ t
    rw [hT]
  -- LHS simplifies to M! · ∏_x [μ_x^{Zx} c^{Tx} / ((Zx−Tx)!·Tx!)]
  have hL : mass M μ (subMM Z T) * wCost c μ T =
      (Nat.factorial M : ℝ) * (∏ x : X,
        μ x ^ Z x * c ^ T x / ((Nat.factorial (Z x - T x) : ℝ) * (Nat.factorial (T x) : ℝ))) := by
    calc
      mass M μ (subMM Z T) * wCost c μ T
          = ((Nat.factorial M : ℝ) * (∏ x : X, μ x ^ (Z x - T x) / (Nat.factorial (Z x - T x) : ℝ)))
              * (∏ x : X, (c * μ x) ^ T x / (Nat.factorial (T x) : ℝ)) := by
              simp [mass, wCost, subMM]
      _ = (Nat.factorial M : ℝ)
              * ((∏ x : X, μ x ^ (Z x - T x) / (Nat.factorial (Z x - T x) : ℝ))
                * (∏ x : X, (c * μ x) ^ T x / (Nat.factorial (T x) : ℝ))) := by
              ring
      _ = (Nat.factorial M : ℝ)
              * (∏ x : X, (μ x ^ (Z x - T x) / (Nat.factorial (Z x - T x) : ℝ))
                  * ((c * μ x) ^ T x / (Nat.factorial (T x) : ℝ))) := by
              rw [← Finset.prod_mul_distrib]
      _ = (Nat.factorial M : ℝ) * (∏ x : X,
            μ x ^ Z x * c ^ T x / ((Nat.factorial (Z x - T x) : ℝ) * (Nat.factorial (T x) : ℝ))) := by
              congr 1
              apply Finset.prod_congr rfl
              intro x hx
              exact coord_prod (μ x) c (Z x) (T x) (hZT x)
  -- RHS also simplifies to M! · ∏_x [μ_x^{Zx} c^{Tx} / ((Zx−Tx)!·Tx!)]
  have hfacMt : (Nat.factorial (M + t) : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero (M + t))
  have hR : mass (M + t) μ Z * ((Nat.factorial M : ℝ) * (Nat.factorial (M + t) : ℝ)⁻¹) *
      c ^ t * (∏ x : X, ((Z x).choose (T x) : ℝ)) =
      (Nat.factorial M : ℝ) * (∏ x : X,
        μ x ^ Z x * c ^ T x / ((Nat.factorial (Z x - T x) : ℝ) * (Nat.factorial (T x) : ℝ))) := by
    calc
      mass (M + t) μ Z * ((Nat.factorial M : ℝ) * (Nat.factorial (M + t) : ℝ)⁻¹) *
          c ^ t * (∏ x : X, ((Z x).choose (T x) : ℝ))
          = ((Nat.factorial (M + t) : ℝ) * (∏ x : X, μ x ^ Z x / (Nat.factorial (Z x) : ℝ)))
              * ((Nat.factorial M : ℝ) * (Nat.factorial (M + t) : ℝ)⁻¹)
              * c ^ t * (∏ x : X, ((Z x).choose (T x) : ℝ)) := by
              simp [mass]
      _ = ((Nat.factorial (M + t) : ℝ) * (Nat.factorial (M + t) : ℝ)⁻¹)
              * ((Nat.factorial M : ℝ) * (∏ x : X, μ x ^ Z x / (Nat.factorial (Z x) : ℝ)))
              * c ^ t * (∏ x : X, ((Z x).choose (T x) : ℝ)) := by
              ring
      _ = (Nat.factorial M : ℝ) * (∏ x : X, μ x ^ Z x / (Nat.factorial (Z x) : ℝ)) *
              c ^ t * (∏ x : X, ((Z x).choose (T x) : ℝ)) := by
              rw [mul_inv_cancel₀ hfacMt]
              ring
      _ = (Nat.factorial M : ℝ) * (∏ x : X, μ x ^ Z x / (Nat.factorial (Z x) : ℝ)) *
              (∏ x : X, c ^ T x) * (∏ x : X, ((Z x).choose (T x) : ℝ)) := by
              rw [← hprodT]
      _ = (Nat.factorial M : ℝ) * (((∏ x : X, μ x ^ Z x / (Nat.factorial (Z x) : ℝ)) *
                (∏ x : X, ((Z x).choose (T x) : ℝ))) * (∏ x : X, c ^ T x)) := by
              ring
      _ = (Nat.factorial M : ℝ) * ((∏ x : X, (μ x ^ Z x / (Nat.factorial (Z x) : ℝ)) *
                ((Z x).choose (T x) : ℝ)) * (∏ x : X, c ^ T x)) := by
              rw [← Finset.prod_mul_distrib]
      _ = (Nat.factorial M : ℝ) * (∏ x : X,
              (μ x ^ Z x / (Nat.factorial (Z x) : ℝ)) * ((Z x).choose (T x) : ℝ) * c ^ T x) := by
              rw [← Finset.prod_mul_distrib]
      _ = (Nat.factorial M : ℝ) * (∏ x : X,
            μ x ^ Z x * c ^ T x / ((Nat.factorial (Z x - T x) : ℝ) * (Nat.factorial (T x) : ℝ))) := by
              congr 1
              apply Finset.prod_congr rfl
              intro x hx
              exact coord_choose (μ x) c (Z x) (T x) (hZT x)
  rw [hL, hR]

lemma wCost_nonneg (c : ℝ) (hc0 : 0 ≤ c) {μ : X → ℝ} (hμ0 : ∀ x, 0 ≤ μ x) (m : X → ℕ) :
    0 ≤ wCost c μ m := by
  unfold wCost
  exact Finset.prod_nonneg (by
    intro x hx
    have h1 : 0 ≤ c * μ x := mul_nonneg hc0 (hμ0 x)
    positivity)

end Multi
end Submission
