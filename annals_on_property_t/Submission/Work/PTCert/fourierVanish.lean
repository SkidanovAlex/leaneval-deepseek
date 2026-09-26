import Mathlib
import Submission.Work.PTCert.GlueDefs
import Submission.Work.PTCert.twistedFourierCriterion

/-! Guidance from the project lead (the requester):

Context: `Submission/Work/PTCert/GlueDefs.lean` (definitions + Props; read it first) glues the
kernel-checked certificate data to the proved generic chain (`Chain.lean`, `Math.lean`,
`Interfaces.lean`; all their Props are already PROVED: avgPrinciple, labelPrinciple, gramSOS,
avgGram, avgMatInvariant, rowFormula, psdOfBlock, psdSignedPerm, ldlScaledPrinciple,
twistedFourierCriterion, residualAbsorption, letterAction, signCodes8, sigmaGroupFacts, modelSound,
permCheckKSound, ...). The design note is `NOTES_LEAD_glue.md` at the workspace root.
Do NOT change GlueDefs.lean. If the statement is false, `declare_false` with a concrete counterexample.
Put helper lemmas in your own file or under `Submission/Work/PTCert/<yourLemma>/`.
Route. Needs only `chiS_add` (multiplicativity, proved in `twistedFourierCriterion.lean` as
`Work.PTCert.chiS_add` or similar — grep `chiS_add`) and the action laws.
Row: for every b, M x (act b y) = M (act a x) (act a (act a (act b y)))? Simpler: since act a x = x,
  M x (act b y) = M (act a x) (act a (act (a + b) y))  [act a ∘ act a = act (a+a) = act 0 = id, char 2]
             = M x (act (a + b) y)  [invariance].
So W := Σ_b χ(b) M x (act b y) = Σ_b χ(b) M x (act (a+b) y) = Σ_c χ(c + a) M x (act c y)  (reindex
c = a + b, Equiv.addLeft) = χ(a) W = -W, hence W = 0.
Column: M y (act b x) = M y (act b (act a x)) = M y (act (b + a) x); same reindexing.
-/

namespace Work.PTCert

open Submission.PTCert

/-- `(Fin m → ZMod 2)` has exponent two. -/
private lemma pi_zmod2_add_self {m : ℕ} (v : Fin m → ZMod 2) : v + v = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (v i)

theorem fourierVanish : FourierVanish := by
  intro m ι act hadd hzero M hM S x a hax hchi y
  constructor
  · -- Row: the summand over `b` is that over `a + b`, and `c ↦ a + c` reindexes onto `χ(a)`.
    have hrow : ∀ b : Fin m → ZMod 2, M x (act b y) = M x (act (a + b) y) := by
      intro b
      have h1 : act b y = act a (act (a + b) y) := by
        rw [← hadd a (a + b) y,
          show a + (a + b) = b from by rw [← add_assoc, pi_zmod2_add_self a, zero_add]]
      have h2 : M x (act a (act (a + b) y)) = M x (act (a + b) y) := by
        have h := hM a x (act (a + b) y)
        rwa [hax] at h
      rw [h1, h2]
    have hstep1 : (∑ b, chiS S b * M x (act b y))
        = ∑ b, chiS S b * M x (act (a + b) y) :=
      Finset.sum_congr rfl (fun b _ => by rw [hrow b])
    have hstep2 : (∑ b, chiS S b * M x (act (a + b) y))
        = ∑ c, chiS S (a + c) * M x (act c y) := by
      have hcong : (∑ b, chiS S b * M x (act (a + b) y))
          = ∑ b, chiS S (a + (a + b)) * M x (act (a + b) y) := by
        apply Finset.sum_congr rfl
        intro b _
        rw [show a + (a + b) = b from by rw [← add_assoc, pi_zmod2_add_self a, zero_add]]
      rw [hcong]
      simpa only [Equiv.coe_addLeft] using
        (Equiv.sum_comp (Equiv.addLeft a) (fun c => chiS S (a + c) * M x (act c y)))
    have hstep3 : (∑ c, chiS S (a + c) * M x (act c y))
        = chiS S a * ∑ c, chiS S c * M x (act c y) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      rw [chiS_add]
      ring
    have key : fourierW act M S x y = chiS S a * fourierW act M S x y := by
      have hchain := hstep1.trans (hstep2.trans hstep3)
      simpa [fourierW] using hchain
    have h1 : fourierW act M S x y = chiS S a * fourierW act M S x y := key
    have h2 : chiS S a * fourierW act M S x y = -(fourierW act M S x y) := by
      rw [hchi]; ring
    linarith
  · -- Column: `act b x = act b (act a x) = act (b + a) x`; same reindexing.
    have hcol : ∀ b : Fin m → ZMod 2, act b x = act (b + a) x := by
      intro b
      rw [hadd b a x, hax]
    have hstep1 : (∑ b, chiS S b * M y (act b x))
        = ∑ b, chiS S b * M y (act (b + a) x) :=
      Finset.sum_congr rfl (fun b _ => by rw [hcol b])
    have hstep2 : (∑ b, chiS S b * M y (act (b + a) x))
        = ∑ c, chiS S (c + a) * M y (act c x) := by
      have hcong : (∑ b, chiS S b * M y (act (b + a) x))
          = ∑ b, chiS S ((b + a) + a) * M y (act (b + a) x) := by
        apply Finset.sum_congr rfl
        intro b _
        rw [show (b + a) + a = b from by
          rw [add_assoc, pi_zmod2_add_self a, add_zero]]
      rw [hcong]
      simpa only [Equiv.coe_addRight] using
        (Equiv.sum_comp (Equiv.addRight a) (fun c => chiS S (c + a) * M y (act c x)))
    have hstep3 : (∑ c, chiS S (c + a) * M y (act c x))
        = chiS S a * ∑ c, chiS S c * M y (act c x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      rw [chiS_add]
      ring
    have key : fourierW act M S y x = chiS S a * fourierW act M S y x := by
      have hchain := hstep1.trans (hstep2.trans hstep3)
      simpa [fourierW] using hchain
    have h1 : fourierW act M S y x = chiS S a * fourierW act M S y x := key
    have h2 : chiS S a * fourierW act M S y x = -(fourierW act M S y x) := by
      rw [hchi]; ring
    linarith

end Work.PTCert
