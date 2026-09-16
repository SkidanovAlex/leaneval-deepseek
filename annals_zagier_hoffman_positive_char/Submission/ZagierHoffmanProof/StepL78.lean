import Submission.ZagierHoffmanProof.StepL77
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
namespace ZagierHoffmanPositiveChar
/-!
# Step L78: CASE-1 j=0 a-side (i ≠ u) member facts (SESSION 227)

The a-members of the CASE-1 empty-front chain (D := BCqIter F 1 (toData R0), i ≠ u)
have tuple D.cA i = q :: (R0.cA i), depth R0.depA i + 1.  Their dispatch facts:
  ★ g5c1_aSide_weight (… hwtA) : weight (D.depA i)(D.cA i) = weight r s — the
      q-prepend weight shift (weight_consVec) + hwtA (weight (R0.cA i) =
      psum r − psum 1 = w − q) + hs0 (psum 1 = q) + omega;
  ★ g5c1_aSide_prefix_drop (… hhead) : psum (D.cA i) 2 < psum s 2 — the q-prepend
      prefix: psum 2 = q + (R0.cA i)⟨0⟩ < q + s₂ via hhead — the recursion's
      l2μ-drop for the ¬2-adm members.
CONSEQUENCE (recorded): every a-side member is 1-admissible (head q ≤ q, depth ≥ 2),
and every ¬2-adm one is in-domain with the strict prefix-2 drop ⟹ dispatched by the
g5 recursion IH; 2-adm ones by self.  b-members are 2-adm (see (b) next).  LEAN:
member lemmas quantify over i : R0.ιA (NOT D.ιA — the D-let-index breaks simp/rw at
reducible transparency); rewrite the tuple first and `change` the depth (rw of the
depth through a dependent weight-arg fails "motive not type correct"); after rw of a
tuple inside psum the implicit depth arg goes stale — use `change` to resync.
-/

attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- a-side (i ≠ u) member weight of the CASE-1 j=0 chain is w (= weight r s):
D.cA i = q :: (R0.cA i), weight (R0.cA i) = psum r − psum 1 = w − q (hwtA), head q. -/
lemma g5c1_aSide_weight (r : ℕ) (s : Fin r → ℕ+) (hcase : 2 ≤ r)
    (hs0 : (s ⟨0, by omega⟩ : ℕ) = Nat.card F)
    (hbig : (Nat.card F : ℕ) < (s ⟨1, by omega⟩ : ℕ))
    (R0 : BinaryRel F) (u : R0.ιA) (hau : R0.aA u = 1)
    (hwtA : ∀ i : R0.ιA, i ≠ u → weight (R0.depA i) (R0.cA i) = psum s r - psum s (2 - 1)) :
    let D := RelData.BCqIter F 1 (toData F R0)
    ∀ i : R0.ιA, i ≠ u → weight (D.depA i) (D.cA i) = weight r s := by
  classical
  intro D i hi
  have hdep : D.depA i = R0.depA i + 1 := by
    dsimp [D, RelData.BCqIter, RelData.BCq]
    rfl
  have hcA : D.cA i = consVec (qExp F) (R0.cA i) := by
    dsimp [D, RelData.BCqIter, RelData.BCq]
    rfl
  rw [hcA]
  change weight (R0.depA i + 1) (consVec (qExp F) (R0.cA i)) = weight r s
  have hwcons : weight (R0.depA i + 1) (consVec (qExp F) (R0.cA i)) =
      (qExp F : ℕ) + weight (R0.depA i) (R0.cA i) := by
    exact weight_consVec (qExp F) (R0.cA i)
  rw [hwcons]
  have hwt := hwtA i hi
  rw [hwt]
  have hpsumr : psum s r = weight r s := psum_self s
  rw [← hpsumr]
  have hpsum1 : psum s 1 = (qExp F : ℕ) := by
    have hp : psum s 1 = pad0 s 0 := by
      change (∑ j ∈ Finset.range 1, pad0 s j) = pad0 s 0
      simp
    rw [hp]
    have hp0 : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < r)
    rw [hp0]
    change (s ⟨0, by omega⟩ : ℕ) = (qExp F : ℕ)
    rw [hs0]
    rfl
  -- goal: (qExp:ℕ) + (psum s r - psum s 1) = weight r s  -- with psum r = weight r s
  have hq : (qExp F : ℕ) = Nat.card F := by rfl
  rw [hq, hpsum1]
  -- (Nat.card F) + (psum s r - psum s 1) = psum s r
  have hle1 : psum s 1 ≤ psum s r := psum_mono s (by omega : 1 ≤ r)
  omega

/-- a-side (i ≠ u) prefix-2 of the CASE-1 j=0 member is STRICTLY less than psum s 2
(q + head(R0.cA i) < q + s₂ via hhead) — the recursion's measure drop. -/
lemma g5c1_aSide_prefix_drop (r : ℕ) (s : Fin r → ℕ+) (hcase : 2 ≤ r)
    (hs0 : (s ⟨0, by omega⟩ : ℕ) = Nat.card F)
    (hbig : (Nat.card F : ℕ) < (s ⟨1, by omega⟩ : ℕ))
    (R0 : BinaryRel F) (u : R0.ιA)
    (hhead : ∀ i : R0.ιA, i ≠ u →
      ((R0.cA i) ⟨0, R0.hdepA i⟩ : ℕ) < (s ⟨2 - 1, by omega⟩ : ℕ)) :
    let D := RelData.BCqIter F 1 (toData F R0)
    ∀ i : R0.ιA, i ≠ u → psum (D.cA i) 2 < psum s 2 := by
  classical
  intro D i hi
  have hdepApos : 0 < R0.depA i := R0.hdepA i
  change psum (consVec (qExp F) (R0.cA i)) 2 < psum s 2
  -- psum (consVec q t) 2 = q + t⟨0, hdepA i⟩
  have hp : psum (consVec (qExp F) (R0.cA i)) 2 =
      (qExp F : ℕ) + ((R0.cA i) ⟨0, R0.hdepA i⟩ : ℕ) := by
    have hpsum2 : psum (consVec (qExp F) (R0.cA i)) 2 =
        pad0 (consVec (qExp F) (R0.cA i)) 0 + pad0 (consVec (qExp F) (R0.cA i)) 1 := by
      change (∑ j ∈ Finset.range 2, pad0 (consVec (qExp F) (R0.cA i)) j) =
        pad0 (consVec (qExp F) (R0.cA i)) 0 + pad0 (consVec (qExp F) (R0.cA i)) 1
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      simp
    rw [hpsum2]
    have hd0 : 0 < R0.depA i + 1 := by omega
    have hp0 : pad0 (consVec (qExp F) (R0.cA i)) 0 = (qExp F : ℕ) := by
      rw [pad0_of_lt (consVec (qExp F) (R0.cA i)) hd0]
      rfl
    have hd1 : 1 < R0.depA i + 1 := by omega
    have hp1 : pad0 (consVec (qExp F) (R0.cA i)) 1 = ((R0.cA i) ⟨0, R0.hdepA i⟩ : ℕ) := by
      rw [pad0_of_lt (consVec (qExp F) (R0.cA i)) hd1]
      rfl
    rw [hp0, hp1]
  rw [hp]
  -- psum s 2 = q + s₂
  have hps2 : psum s 2 = (qExp F : ℕ) + (s ⟨1, by omega⟩ : ℕ) := by
    have hpsum2 : psum s 2 = pad0 s 0 + pad0 s 1 := by
      change (∑ j ∈ Finset.range 2, pad0 s j) = pad0 s 0 + pad0 s 1
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      simp
    rw [hpsum2]
    have hp0 : pad0 s 0 = (qExp F : ℕ) := by
      rw [pad0_of_lt s (by omega : 0 < r)]
      change (s ⟨0, by omega⟩ : ℕ) = (qExp F : ℕ)
      rw [hs0]
      rfl
    have hp1 : pad0 s 1 = (s ⟨1, by omega⟩ : ℕ) := by
      rw [pad0_of_lt s (by omega : 1 < r)]
    rw [hp0, hp1]
  rw [hps2]
  have hh := hhead i hi
  change (qExp F : ℕ) + ((R0.cA i) ⟨0, R0.hdepA i⟩ : ℕ) <
    (qExp F : ℕ) + (s ⟨2 - 1, by omega⟩ : ℕ)
  omega

end ZagierHoffmanPositiveChar
