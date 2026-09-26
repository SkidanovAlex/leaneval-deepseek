import Mathlib
import Submission.Work.PTCert.GlueDefs
import Submission.Work.PTCert.twistedFourierCriterion
import Submission.Work.PTCert.fourierVanish
import Submission.Work.PTCert.psdOfBlock
import Submission.Work.PTCert.Klein.wActFst
import Submission.Work.PTCert.Klein.wActSnd
import Submission.Work.PTCert.Klein.wSymm
import Submission.Work.PTCert.Klein.wKap
import Submission.Work.PTCert.Klein.kapRepFst
import Submission.Work.PTCert.Klein.admKap
import Submission.Work.PTCert.Klein.nuAct

/-! Guidance from the project lead (the requester):

Context: `Submission/Work/PTCert/GlueDefs.lean` (definitions + Props; read it first) glues the
kernel-checked certificate data to the proved generic chain (`Chain.lean`, `Math.lean`,
`Interfaces.lean`; all their Props are already PROVED: avgPrinciple, labelPrinciple, gramSOS,
avgGram, avgMatInvariant, rowFormula, psdOfBlock, psdSignedPerm, ldlScaledPrinciple,
twistedFourierCriterion, residualAbsorption, letterAction, signCodes8, sigmaGroupFacts, modelSound,
permCheckKSound, ...). The design note is `NOTES_LEAD_glue.md` at the workspace root.
Do NOT change GlueDefs.lean. If the statement is false, `declare_false` with a concrete counterexample.
Put helper lemmas in your own file or under `Submission/Work/PTCert/<yourLemma>/`.
This is the second level of the sign-character Fourier reduction. It is a composition of the PROVED
generic lemmas; the work is to verify their hypotheses.

(The guidance comment of the original request is reproduced here; the helpers used are
`Work.PTCert.Klein.wActFst`, `wActSnd`, `wSymm`, `wKap`, `kapRepFst`, `admKap`, `nuAct` and
`Work.PTCert.fourierVanish`, `Work.PTCert.twistedFourierCriterion`, `Work.PTCert.psdOfBlock`.)
-/

open Submission.PTCert
open scoped BigOperators

set_option autoImplicit false

namespace Work.PTCert

open Submission.PTCert

private lemma pi_add_self {m : ℕ} (b : Fin m → ZMod 2) : b + b = 0 := by
  funext i; exact CharTwo.add_self_eq_zero (b i)

theorem kleinLevel : KleinLevel := by
  intro m m2 ι instF instD act kap θ hact hact0 hkap hkap0 hcomm hθ S hchiθ M hMsym hMinv hMkap
    rep nu hactnu hreprep hrepact ks hksadm hksdist hkscover
  haveI : Fintype ι := instF
  haveI : DecidableEq ι := instD
  classical
  constructor
  · -- ============ symmetry conjunct ============
    intro ψ i j
    refine Finset.sum_congr rfl (fun b _ => ?_)
    have hsqj : chiS S (nu (kap b (ks.get j))) * chiS S (nu (kap b (ks.get j))) = 1 :=
      chiS_sq S _
    have hsqi : chiS S (nu (kap b (ks.get i))) * chiS S (nu (kap b (ks.get i))) = 1 :=
      chiS_sq S _
    have h1 : fourierW act M S (ks.get i) (rep (kap b (ks.get j)))
        = chiS S (nu (kap b (ks.get j))) * fourierW act M S (ks.get i) (kap b (ks.get j)) := by
      have h := Klein.wActSnd act M S hact (nu (kap b (ks.get j))) (ks.get i) (rep (kap b (ks.get j)))
      rw [hactnu (kap b (ks.get j))] at h
      rw [h, ← mul_assoc, hsqj, one_mul]
    have h2 : fourierW act M S (ks.get j) (rep (kap b (ks.get i)))
        = chiS S (nu (kap b (ks.get i))) * fourierW act M S (ks.get j) (kap b (ks.get i)) := by
      have h := Klein.wActSnd act M S hact (nu (kap b (ks.get i))) (ks.get j) (rep (kap b (ks.get i)))
      rw [hactnu (kap b (ks.get i))] at h
      rw [h, ← mul_assoc, hsqi, one_mul]
    have h3 : fourierW act M S (ks.get i) (kap b (ks.get j))
        = fourierW act M S (ks.get j) (kap b (ks.get i)) := by
      have hw := Klein.wKap act kap θ M S hcomm hθ hchiθ hMkap b (kap b (ks.get i)) (ks.get j)
      rw [← hkap b b (ks.get i), pi_add_self (m := m2) b, hkap0] at hw
      rw [hw, Klein.wSymm act M S hMsym hact hact0 hMinv (ks.get j) (kap b (ks.get i))]
    calc chiS ψ b * chiS S (nu (kap b (ks.get j))) * fourierW act M S (ks.get i) (rep (kap b (ks.get j)))
        = chiS ψ b * (chiS S (nu (kap b (ks.get j))) * chiS S (nu (kap b (ks.get j))))
            * fourierW act M S (ks.get i) (kap b (ks.get j)) := by rw [h1]; ring
      _ = chiS ψ b * fourierW act M S (ks.get i) (kap b (ks.get j)) := by rw [hsqj]; ring
      _ = chiS ψ b * fourierW act M S (ks.get j) (kap b (ks.get i)) := by rw [h3]
      _ = chiS ψ b * (chiS S (nu (kap b (ks.get i))) * chiS S (nu (kap b (ks.get i))))
            * fourierW act M S (ks.get j) (kap b (ks.get i)) := by rw [hsqi]; ring
      _ = chiS ψ b * chiS S (nu (kap b (ks.get i))) * fourierW act M S (ks.get j) (rep (kap b (ks.get i))) := by
            rw [h2]; ring
  · -- ============ PSD conjunct ============
    intro hpsi
    set A : Type := {x : ι // rep x = x ∧ ∀ a, act a x = x → chiS S a = 1} with hA
    haveI : Fintype A := by rw [hA]; infer_instance
    haveI : DecidableEq A := by rw [hA]; infer_instance
    set kbar : (Fin m2 → ZMod 2) → A → A := fun b x =>
      ⟨rep (kap b x.1), hreprep (kap b x.1),
        Klein.admKap act kap θ nu rep S hact hactnu hcomm hkap hkap0 hchiθ x.1 x.2.1 x.2.2 b⟩ with hkbar
    set sgn2 : (Fin m2 → ZMod 2) → A → ℝ := fun b x => chiS S (nu (kap b x.1)) with hsgn2def
    set M2 : Matrix A A ℝ := Matrix.of fun x y => fourierW act M S x.1 y.1 with hM2def
    have hkbar_val : ∀ (b : Fin m2 → ZMod 2) (x : A), (kbar b x).1 = rep (kap b x.1) := fun b x => rfl
    have hkbar_add : ∀ (a b : Fin m2 → ZMod 2) (x : A), kbar (a + b) x = kbar a (kbar b x) := by
      intro a b x
      apply Subtype.ext
      simp only [hkbar_val]
      rw [hkap a b x.1, ← Klein.kapRepFst act kap θ nu rep hact hactnu hrepact hcomm a (kap b x.1)]
    have hkbar_zero : ∀ x : A, kbar 0 x = x := by
      intro x
      apply Subtype.ext
      simp only [hkbar_val]
      rw [hkap0, x.2.1]
    have hcover : ∀ x : A, ∃ (i : Fin ks.length) (b : Fin m2 → ZMod 2), rep (kap b (ks.get i)) = x.1 :=
      fun x => hkscover x.1 x.2.1 x.2.2
    set ix : A → Fin ks.length := fun x => Classical.choose (hcover x) with hix
    set bx : A → (Fin m2 → ZMod 2) := fun x => Classical.choose (Classical.choose_spec (hcover x)) with hbx
    have hbx_spec : ∀ x : A, rep (kap (bx x) (ks.get (ix x))) = x.1 := by
      intro x
      rw [hbx, hix]
      exact Classical.choose_spec (Classical.choose_spec (hcover x))
    set rep2 : A → A := fun x => ⟨ks.get (ix x), hksadm (ks.get (ix x)) (List.get_mem ks (ix x))⟩ with hrep2def
    have hrep2_val : ∀ x : A, (rep2 x).1 = ks.get (ix x) := fun x => rfl
    have huniq : ∀ (i j : Fin ks.length) (b b' : Fin m2 → ZMod 2),
        rep (kap b (ks.get i)) = rep (kap b' (ks.get j)) → i = j := by
      intro i j b b' h
      have h2 : rep (kap b' (rep (kap b (ks.get i)))) = rep (kap b' (rep (kap b' (ks.get j)))) := by
        rw [h]
      rw [Klein.kapRepFst act kap θ nu rep hact hactnu hrepact hcomm b' (kap b (ks.get i)),
          Klein.kapRepFst act kap θ nu rep hact hactnu hrepact hcomm b' (kap b' (ks.get j))] at h2
      rw [← hkap b' b (ks.get i), ← hkap b' b' (ks.get j), pi_add_self b', hkap0] at h2
      rw [(hksadm (ks.get j) (List.get_mem ks j)).1] at h2
      exact hksdist i j (b' + b) h2
    have hix_rep2 : ∀ x : A, ix (rep2 x) = ix x := by
      intro x
      apply huniq (ix (rep2 x)) (ix x) (bx (rep2 x)) 0
      rw [hbx_spec (rep2 x), hrep2_val x, hkap0, (hksadm (ks.get (ix x)) (List.get_mem ks (ix x))).1]
    have hrep2idem : ∀ x : A, rep2 (rep2 x) = rep2 x := by
      intro x
      apply Subtype.ext
      simp only [hrep2_val]
      rw [hix_rep2 x]
    have hrepact2 : ∀ (b : Fin m2 → ZMod 2) (x : A), rep2 (kbar b x) = rep2 x := by
      intro b x
      apply Subtype.ext
      simp only [hrep2_val]
      have hix' : ix (kbar b x) = ix x := by
        apply huniq (ix (kbar b x)) (ix x) (bx (kbar b x)) (b + bx x)
        rw [hbx_spec (kbar b x), hkbar_val b x, ← hbx_spec x,
            Klein.kapRepFst act kap θ nu rep hact hactnu hrepact hcomm b (kap (bx x) (ks.get (ix x))),
            ← hkap b (bx x) (ks.get (ix x))]
      rw [hix']
    have hactnu2 : ∀ x : A, kbar (bx x) (rep2 x) = x := by
      intro x
      apply Subtype.ext
      rw [hkbar_val, hrep2_val]
      exact hbx_spec x
    have hsgn2 : ∀ (a b : Fin m2 → ZMod 2) (x : A), sgn2 (a + b) x = sgn2 a (kbar b x) * sgn2 b x := by
      intro a b x
      simp only [hsgn2def, hkbar_val]
      have hzz : rep (kap a (rep (kap b x.1))) = rep (kap (a + b) x.1) := by
        rw [hkap a b x.1]
        exact Klein.kapRepFst act kap θ nu rep hact hactnu hrepact hcomm a (kap b x.1)
      have hadm : ∀ a', act a' (rep (kap a (rep (kap b x.1)))) = rep (kap a (rep (kap b x.1))) → chiS S a' = 1 :=
        Klein.admKap act kap θ nu rep S hact hactnu hcomm hkap hkap0 hchiθ
          (kbar b x).1 (kbar b x).2.1 (kbar b x).2.2 a
      have hz' : kap (a + b) x.1 = act (θ a (nu (kap b x.1))) (kap a (rep (kap b x.1))) := by
        calc kap (a + b) x.1 = kap a (kap b x.1) := hkap a b x.1
          _ = kap a (act (nu (kap b x.1)) (rep (kap b x.1))) := by rw [hactnu (kap b x.1)]
          _ = act (θ a (nu (kap b x.1))) (kap a (rep (kap b x.1))) :=
                hcomm a (nu (kap b x.1)) (rep (kap b x.1))
      have hmain := Klein.nuAct act nu rep S hact hact0 hactnu hzz hadm (θ a (nu (kap b x.1))) hz'
      rw [hmain, hchiθ a (nu (kap b x.1))]
      ring
    have hM2sym : M2.transpose = M2 := by
      rw [hM2def]
      ext x y
      simp only [Matrix.transpose_apply, Matrix.of_apply]
      exact Klein.wSymm act M S hMsym hact hact0 hMinv x.1 y.1
    have hM2inv : ∀ (a : Fin m2 → ZMod 2) (x y : A),
        sgn2 a x * sgn2 a y * M2 (kbar a x) (kbar a y) = M2 x y := by
      intro a x y
      simp only [hsgn2def, hkbar_val, hM2def, Matrix.of_apply]
      have h1 : fourierW act M S (kap a x.1) (rep (kap a y.1))
          = chiS S (nu (kap a x.1)) * fourierW act M S (rep (kap a x.1)) (rep (kap a y.1)) := by
        have h := Klein.wActFst act M S hact hact0 hMinv (nu (kap a x.1)) (rep (kap a x.1)) (rep (kap a y.1))
        rwa [hactnu (kap a x.1)] at h
      have h2 : fourierW act M S (kap a x.1) (kap a y.1)
          = chiS S (nu (kap a y.1)) * fourierW act M S (kap a x.1) (rep (kap a y.1)) := by
        have h := Klein.wActSnd act M S hact (nu (kap a y.1)) (kap a x.1) (rep (kap a y.1))
        rwa [hactnu (kap a y.1)] at h
      calc chiS S (nu (kap a x.1)) * chiS S (nu (kap a y.1))
              * fourierW act M S (rep (kap a x.1)) (rep (kap a y.1))
          = chiS S (nu (kap a y.1))
              * (chiS S (nu (kap a x.1)) * fourierW act M S (rep (kap a x.1)) (rep (kap a y.1))) := by ring
        _ = chiS S (nu (kap a y.1)) * fourierW act M S (kap a x.1) (rep (kap a y.1)) := by rw [← h1]
        _ = fourierW act M S (kap a x.1) (kap a y.1) := by rw [← h2]
        _ = fourierW act M S x.1 y.1 := Klein.wKap act kap θ M S hcomm hθ hchiθ hMkap a x.1 y.1
    have hblocks : ∀ ψ : Finset (Fin m2),
        (Matrix.of fun (x y : {x : A // rep2 x = x}) =>
          ∑ a, chiS ψ a * sgn2 a y.1 * M2 x.1 (kbar a y.1)).PosSemidef := by
      intro ψ
      set idx : {x : A // rep2 x = x} → Fin ks.length := fun x => ix x.1 with hidx
      have hidx_val : ∀ x : {x : A // rep2 x = x}, ks.get (idx x) = x.1.1 := by
        intro x
        have h := congrArg Subtype.val x.2
        rw [hrep2_val] at h
        rw [hidx]
        exact h
      have hmat : (Matrix.of fun (x y : {x : A // rep2 x = x}) =>
            ∑ a, chiS ψ a * sgn2 a y.1 * M2 x.1 (kbar a y.1))
          = (Matrix.of fun (i j : Fin ks.length) =>
              ∑ b, chiS ψ b * chiS S (nu (kap b (ks.get j))) *
                fourierW act M S (ks.get i) (rep (kap b (ks.get j)))).submatrix idx idx := by
        ext x y
        simp only [Matrix.submatrix_apply, Matrix.of_apply, hsgn2def, hM2def, hkbar_val]
        rw [hidx_val x, hidx_val y]
      rw [hmat]
      exact (hpsi ψ).submatrix idx
    have hsgn2val : ∀ (a : Fin m2 → ZMod 2) (x : A), sgn2 a x = 1 ∨ sgn2 a x = -1 :=
      fun a x => chiS_pm S (nu (kap a x.1))
    have hM2psd : M2.PosSemidef :=
      twistedFourierCriterion m2 kbar sgn2 hkbar_add hkbar_zero hsgn2 hsgn2val M2 hM2sym hM2inv
        rep2 bx hactnu2 hrep2idem hrepact2 hblocks
    -- transport to all `rep`-fixed points
    set Sfin : Finset {z : ι // rep z = z} :=
      Finset.univ.filter (fun z => ∀ a, act a z.1 = z.1 → chiS S a = 1) with hSfin
    have hSfin_mem : ∀ z : {z : ι // rep z = z},
        (z ∈ Sfin) ↔ (∀ a, act a z.1 = z.1 → chiS S a = 1) := by
      intro z
      rw [hSfin]
      simp
    have hrow : ∀ x y : {z : ι // rep z = z}, x ∉ Sfin →
        (Matrix.of fun (x y : {z : ι // rep z = z}) => fourierW act M S x.1 y.1) x y = 0 := by
      intro x y hx
      have hx' : ¬ (∀ a, act a x.1 = x.1 → chiS S a = 1) := fun hh => hx ((hSfin_mem x).mpr hh)
      push_neg at hx'
      obtain ⟨a, ha, hne⟩ := hx'
      have hneg : chiS S a = -1 := by
        rcases chiS_pm S a with h | h
        · exact absurd h hne
        · exact h
      exact (fourierVanish m act hact hact0 M hMinv S x.1 a ha hneg y.1).1
    have hcol : ∀ x y : {z : ι // rep z = z}, y ∉ Sfin →
        (Matrix.of fun (x y : {z : ι // rep z = z}) => fourierW act M S x.1 y.1) x y = 0 := by
      intro x y hy
      have hy' : ¬ (∀ a, act a y.1 = y.1 → chiS S a = 1) := fun hh => hy ((hSfin_mem y).mpr hh)
      push_neg at hy'
      obtain ⟨a, ha, hne⟩ := hy'
      have hneg : chiS S a = -1 := by
        rcases chiS_pm S a with h | h
        · exact absurd h hne
        · exact h
      exact (fourierVanish m act hact hact0 M hMinv S y.1 a ha hneg x.1).2
    have hblk : (Matrix.of fun (x y : Sfin) =>
        (Matrix.of fun (x y : {z : ι // rep z = z}) => fourierW act M S x.1 y.1) x.1 y.1).PosSemidef :=
      hM2psd.submatrix (fun x : Sfin =>
        (⟨x.1.1, x.1.2, (hSfin_mem x.1).mp x.2⟩ : A))
    exact psdOfBlock (Matrix.of fun (x y : {z : ι // rep z = z}) => fourierW act M S x.1 y.1)
      Sfin hrow hcol hblk

end Work.PTCert
