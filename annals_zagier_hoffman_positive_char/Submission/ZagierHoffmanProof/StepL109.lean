import Submission.ZagierHoffmanProof.StepL108
import Submission.ZagierHoffmanProof.StepL32
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L109: \u2605 maink_zeta_kk1 \u2014 the (k, k\u22121) CASE-1 \u03b6-core at SYMBOLIC k
(SESSION 255)

theorem maink_zeta_kk1 (r k s hk1 hk2 hkr hbig hsj R0 u hau hdepu hc0 hbhd) :
  the (k, k\u22121) chain \u03b6-identity \u03b6(s) + guarded-type-1 + type-2 + type-3 = 0
  \u2014 zeta_214_reindexed at (k, k\u22121) (hj1 : 1 \u2264 k\u22121, hjk : k\u22121 \u2264 k\u22121,
  hmid VACUOUS, hsj : s\u27e8(k\u22121)\u22121\u27e9 < q) repackaged over maink_config_full's
  data.  LEAN LESSON: at SYMBOLIC k the chain lets DO NOT reduce (k\u2212(k\u22121)\u22121
  \u2260 0, (k\u22121)\u22121 \u2260 k\u22122 syntactically) \u2014 so the statement must keep the
  zeta_214_exact let-forms (D := BCqIter F (k\u2212(k\u22121)\u22121), head s\u27e8(k\u22121)\u22121\u27e9,
  iterIdx F (k\u2212(k\u22121)\u22121), front sPrefix r s (k\u22121)) and hsj about
  s\u27e8k\u22121\u22121\u27e9; then simpa [D, Bs, Q] closes (no arithmetic needed).
NEXT (recorded): the (k, k\u22121) splice body on this \u03b6-core + maink_config_full:
the 3-family fold, per-member e (the k-symbolic member (k\u22121)-adm / drop
dispatch \u2014 the resisting conjunct), horder via type*_psum_ge_k_le at (k,k\u22121),
admExpT_combine F w k; then CASE-2 via prop213_step1 at (k,k\u22121), A(k)@w via
lk_induction (StepL107); theorem_A's span at weight w via A(w)@w + the
T-membership bridge + Counting.theorem_A_of_span.  theorem_B/D remain ABP-gated.
-/

namespace ZagierHoffmanPositiveChar
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ The (k, k−1) CASE-1 ζ-core: zeta_214_reindexed instantiated at
(k, k−1) with the vacuous hmid, repackaged over the config data of
maink_config_full.  D := BCqIter F 0 (toData R0), B* head s⟨k−2⟩, front
sPrefix r s (k−1); the relation ζ(s) + guarded-type-1 + type-2 + type-3 = 0. -/
theorem maink_zeta_kk1 (r k : ℕ) (s : Fin r → ℕ+) (hk1 : 1 ≤ k) (hk2 : 2 ≤ k) (hkr : k ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨k - 1 - 1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F) (u : R0.ιA)
    (hau : R0.aA u = 1)
    (hdepu : R0.depA u = (r - k) + 1)
    (hc0 : ∀ hd : R0.depA u = (r - k) + 1,
        (fun x : Fin ((r - k) + 1) => R0.cA u (Fin.cast hd.symm x)) =
          bstarBase F r s k hk1 hkr hbig)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - (k - 1) - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨k - 1 - 1, by omega⟩) (fun e => BCqIter_valid F (k - (k - 1) - 1) R0 e)
        (RelData.iterate_merge_hv F (k - (k - 1) - 1) R0 (s ⟨k - 1 - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s (k - 1) (by omega) (by omega))
    ζ_A F s +
      (∑ i : R0.ιA, (if i = u then 0 else
        (((Q.a (Sum.inl (RelData.iterIdx F (k - (k - 1) - 1) (toData F R0) i)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
          ζ_A F (Q.c (Sum.inl (RelData.iterIdx F (k - (k - 1) - 1) (toData F R0) i)))))) +
      (∑ i : D.ιB, (((Q.a (Sum.inr (Sum.inl i)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
          ζ_A F (Q.c (Sum.inr (Sum.inl i))))) +
      (∑ i : D.ιB, (((Q.a (Sum.inr (Sum.inr i)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
          ζ_A F (Q.c (Sum.inr (Sum.inr i))))) = 0 := by
  classical
  intro D Bs Q
  have hz := zeta_214_reindexed F r s k (k - 1) hk1 hkr (by omega : 1 ≤ k - 1)
    (by omega : k - 1 ≤ k - 1) hbig hsj
    (fun i hi1 hi2 => by omega) R0 u hau hdepu hc0 hbhd
  simpa [D, Bs, Q] using hz

end ZagierHoffmanPositiveChar
