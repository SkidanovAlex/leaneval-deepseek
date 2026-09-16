import Submission.ZagierHoffmanProof.StepL1
import Submission.ZagierHoffmanProof.StepK34

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial
open scoped BigOperators

/-!
# Step L2: first ζ-level applications of the bridge (paper §2.2/§2.3, base cases)

`zeta_R1` is the sum of the fundamental relation R1 = (2.8) over all levels: the
ζ-level identity `ζ_A(q) + D1·ζ_A(1, q−1) = 0`.  It is the base case of the paper's
§3 algorithm (tuples of the form `(q)` reduce to the 𝒯-tuple `(1, q−1)`), and it
exercises the whole `zeta_mixed_bridge` pipeline (summable-S, level-0 vanishing,
finite-sum/tsum commutation, shift by one).
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- `D1 = X^q − X` as an element of `K = RatFunc F`. -/
noncomputable def D1rat : RatFunc F := ((carlitzOne F : F[X]) : RatFunc F)

/-- `D1c` (the completion image) equals the image of `D1rat`. -/
lemma D1c_eq_D1rat : D1c F = (D1rat F : RatFunc.CompletionAtInfty F) := by
  simp [D1c, D1rat]

-- ζ-level R1: ζ_A(q) + D1·ζ_A(1, q−1) = 0 (sum of (2.8) over all levels).
theorem zeta_R1 :
    ζ_A F (single (qExp F)) + D1c F * ζ_A F (pair oneExp (qMinusExp F)) = 0 := by
  classical
  let K := RatFunc.CompletionAtInfty F
  have hrel : ∀ d : ℕ,
      (∑ i : Fin 1, ((1 : RatFunc F) : K) * S F 1 (by omega : 0 < 1) (single (qExp F)) d) +
      (∑ j : Fin 1, ((D1rat F : RatFunc F) : K) * S F 2 (by omega : 0 < 2) (pair oneExp (qMinusExp F)) (d + 1)) = 0 := by
    intro d
    have hS1 : S F 1 (by omega : 0 < 1) (single (qExp F)) d = P F d (qExp F) := by
      simpa [single] using (S_one_eq_P F d (by omega : 0 < 1) (single (qExp F)))
    have hr1 := R1_all_unc F d
    simp [R1Prop, D1c, D1rat] at hr1
    -- hr1 : P F d (qExp F) + ((D1rat F : RatFunc F) : K) * S F 2 ⋯ (pair …) (d+1) = 0
    rw [← hS1] at hr1
    simp [D1rat] at hr1 ⊢
    exact hr1
  have hbr := zeta_mixed_bridge F
      (depA := fun _ : Fin 1 => 1) (hdepA := fun _ => by omega)
      (cA := fun _ => single (qExp F)) (aA := fun _ => (1 : RatFunc F))
      (depB := fun _ : Fin 1 => 2) (hdepB := fun _ => by omega)
      (cB := fun _ => pair oneExp (qMinusExp F)) (aB := fun _ => D1rat F)
      (h0B := fun j => S_two_zero F (pair oneExp (qMinusExp F)))
      hrel
  -- hbr : (Σ i : PUnit, 1·ζ_A(single (qExp F))) + (Σ j : PUnit, D1rat·ζ_A(pair …)) = 0
  simpa [D1c_eq_D1rat F, single] using hbr


-- recursion identity for the depth-2 tuple (1, q−1) at level e:
-- S_e(1, q−1) = P_e(1)·S_<e(q−1)   [S_d_recursion at depth 2]
lemma S2_recursion (e : ℕ) :
    S F 2 (by omega : 0 < 2) (pair oneExp (qMinusExp F)) e =
      P F e oneExp * S_lt F 1 (by omega : 0 < 1) (single (qMinusExp F)) e := by
  let 𝔱12 : Fin 2 → ℕ+ := pair oneExp (qMinusExp F)
  let c : RatFunc.CompletionAtInfty F := S_lt F 1 (by omega : 0 < 1) (single (qMinusExp F)) e
  have hrec12 : S F 2 (by omega : 0 < 2) 𝔱12 e = P F e oneExp * c := by
    rw [S_d_recursion F 2 (by omega : 1 < 2) (by omega : 0 < 2) (by omega : 0 < 1) 𝔱12 e]
    congr 1
  simpa [𝔱12, c, single] using hrec12

/-- Display form of Lemma 2.9's CW(R1) before product expansion (paper §2.2):
multiplying R1 = (2.8) by `S_<d+1(W)` and expanding `S_{d+1}(1, q−1)` by the recursion
identity gives, for every tuple `W` of depth `≥ 1` and every level `d`:
    S_d(q)·S_<d+1(W) + D1·S_{d+1}(1)·S_<d+1(q−1)·S_<d+1(W) = 0 .
-/
theorem cw_r1_display {m : ℕ} (hm : 0 < m) (W : Fin m → ℕ+) :
    ∀ d : ℕ,
      (P F d (qExp F)) * S_lt F m hm W (d + 1) +
        D1c F * ((P F (d + 1) oneExp) *
          (S_lt F 1 (by omega : 0 < 1) (single (qMinusExp F)) (d + 1) *
            S_lt F m hm W (d + 1))) = 0 := by
  intro d
  let K := RatFunc.CompletionAtInfty F
  have hr1 := R1_all_unc F d
  have hS2 := S2_recursion F (d + 1)
  calc
    (P F d (qExp F)) * S_lt F m hm W (d + 1) +
        D1c F * ((P F (d + 1) oneExp) *
          (S_lt F 1 (by omega : 0 < 1) (single (qMinusExp F)) (d + 1) * S_lt F m hm W (d + 1)))
        = (P F d (qExp F)) * S_lt F m hm W (d + 1) +
            (D1c F * S F 2 (by omega : 0 < 2) (pair oneExp (qMinusExp F)) (d + 1)) *
              S_lt F m hm W (d + 1) := by
          rw [hS2]
          ring
    _ = (P F d (qExp F) + D1c F * S F 2 (by omega : 0 < 2) (pair oneExp (qMinusExp F)) (d + 1)) *
          S_lt F m hm W (d + 1) := by ring
    _ = 0 := by
          have hr1' : P F d (qExp F) + D1c F * S F 2 (by omega : 0 < 2) (pair oneExp (qMinusExp F)) (d + 1) = 0 := by
            simpa [R1Prop] using hr1
          rw [hr1']
          simp

end ZagierHoffmanPositiveChar
