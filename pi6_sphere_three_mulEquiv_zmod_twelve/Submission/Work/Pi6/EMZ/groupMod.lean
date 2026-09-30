import Mathlib
import Submission.Work.Pi6.EMZ.Defs
import Submission.Work.Pi6.EMZ.moduleFiniteFG
import Submission.Work.StemsB.fg_abelian_decomposition
import Submission.Work.Pi6.EMZ.freePart
import Submission.Work.Pi6.EMZ.finiteTrivial
import Submission.Work.Pi6.EMZ.quotTorsEquiv
import Submission.Work.Pi6.EMZ.finiteZModTwo
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.Pi6.EMZ

noncomputable section

/-!
# `Work.Pi6.EMZ.groupMod`

The two pure group-theoretic bridges used by the integral-table argument (AREA EMZ):

* if a finitely generated abelian group `G` is `p`-divisible for every prime `p` and has no odd
  torsion, then `G = 0`;
* if moreover `|G/2G| ≤ 2` and `2G` misses some element of order `2`, then `G ≅ ℤ/2`.

Both are proved by writing `G ≃+ ℤ^r × F` with `F` finite
(`Work.StemsB.fg_abelian_decomposition`).  The hypotheses are transported along this isomorphism
(`Work.Pi6.EMZ.quotTorsEquiv`), the free part is killed by `Work.Pi6.EMZ.freePart` (a `p`-divisible
`ℤ^r` with `p ≥ 2` has `r = 0`), and the finite part is handled by `Work.Pi6.EMZ.finiteTrivial`
(part 1) and `Work.Pi6.EMZ.finiteZModTwo` (part 2).
-/

theorem groupMod :
    (∀ (G : Type) [AddCommGroup G] (m : Module ℤ G) (h : @Module.Finite ℤ G _ _ m),
      Subsingleton (G ⧸ Work.Pi6.EMZ.pH 2 G) →
      (∀ p : ℕ, p.Prime → p ≠ 2 → Subsingleton (G ⧸ Work.Pi6.EMZ.pH p G)) →
      (∀ p : ℕ, p.Prime → p ≠ 2 → Subsingleton (Work.Pi6.EMZ.torsP p G)) →
      Subsingleton G) ∧
    (∀ (G : Type) [AddCommGroup G] (m : Module ℤ G) (h : @Module.Finite ℤ G _ _ m),
      Nat.card (G ⧸ Work.Pi6.EMZ.pH 2 G) ≤ 2 →
      (∀ p : ℕ, p.Prime → p ≠ 2 → Subsingleton (G ⧸ Work.Pi6.EMZ.pH p G)) →
      (∀ p : ℕ, p.Prime → p ≠ 2 → Subsingleton (Work.Pi6.EMZ.torsP p G)) →
      (∃ a : G, 2 • a = 0 ∧ ∀ b : G, 2 • b ≠ a) →
      Nonempty (G ≃+ ZMod 2)) := by
  constructor
  · -- ### Part 1: `G` is trivial
    intro G _ m h h2 hdiv htor
    have hFG : AddGroup.FG G := moduleFiniteFG m h
    haveI : Module.Finite ℤ G := h
    obtain ⟨r, F, hFadd, hFfin, ⟨e⟩⟩ := Work.StemsB.fg_abelian_decomposition G
    -- transport the hypotheses along `e`
    have h2' : ∀ x : (Fin r → ℤ) × F, ∃ y, 2 • y = x :=
      (quotTorsEquiv e 2).1.mp (subsingleton_quot_pH_iff.mp h2)
    have hdiv' : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ x : (Fin r → ℤ) × F, ∃ y, p • y = x :=
      fun p hp hp2 => (quotTorsEquiv e p).1.mp (subsingleton_quot_pH_iff.mp (hdiv p hp hp2))
    have htor' : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ x : (Fin r → ℤ) × F, p • x = 0 → x = 0 :=
      fun p hp hp2 => (quotTorsEquiv e p).2.1.mp (subsingleton_torsP_iff.mp (htor p hp hp2))
    -- the free part is trivial
    have hr : r = 0 := (freePart (r := r) (p := 2) (by norm_num)).mp <| by
      intro x
      obtain ⟨z, hz⟩ := h2' (x, 0)
      exact ⟨z.1, by
        have := congrArg Prod.fst hz
        simpa using this⟩
    -- so is the finite part
    have hF2 : ∀ x : F, ∃ y : F, 2 • y = x := by
      intro x
      obtain ⟨z, hz⟩ := h2' (0, x)
      exact ⟨z.2, by
        have := congrArg Prod.snd hz
        simpa using this⟩
    have hFdiv : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ x : F, ∃ y : F, p • y = x := by
      intro p hp hp2 x
      obtain ⟨z, hz⟩ := hdiv' p hp hp2 (0, x)
      exact ⟨z.2, by
        have := congrArg Prod.snd hz
        simpa using this⟩
    have hFtor : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ x : F, p • x = 0 → x = 0 := by
      intro p hp hp2 x hx
      have hz := htor' p hp hp2 (0, x) (by
        rw [show (0 : (Fin r → ℤ) × F) = (0, 0) from rfl, Prod.smul_mk]
        ext <;> simp [hx])
      exact congrArg Prod.snd hz
    have hFsub : Subsingleton F := finiteTrivial F hF2 hFdiv hFtor
    subst hr
    exact ⟨fun x y => e.injective (Subsingleton.elim (e x) (e y))⟩
  · -- ### Part 2: `G ≅ ℤ/2`
    intro G _ m h hcard2 hdiv htor ha
    have hFG : AddGroup.FG G := moduleFiniteFG m h
    haveI : Module.Finite ℤ G := h
    obtain ⟨r, F, hFadd, hFfin, ⟨e⟩⟩ := Work.StemsB.fg_abelian_decomposition G
    -- odd divisibility kills the free part
    have h3 : ∀ x : (Fin r → ℤ) × F, ∃ y, 3 • y = x :=
      (quotTorsEquiv e 3).1.mp (subsingleton_quot_pH_iff.mp (hdiv 3 (by norm_num) (by norm_num)))
    have hr : r = 0 := (freePart (r := r) (p := 3) (by norm_num)).mp <| by
      intro x
      obtain ⟨z, hz⟩ := h3 (x, 0)
      exact ⟨z.1, by
        have := congrArg Prod.fst hz
        simpa using this⟩
    subst hr
    let e' : G ≃+ F := e.trans AddEquiv.uniqueProd
    have hcardF : Nat.card (F ⧸ pH 2 F) ≤ 2 := by
      have hh := (quotTorsEquiv e' 2).2.2.2.2
      rw [← hh]; exact hcard2
    have hFdiv : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ x : F, ∃ y : F, p • y = x :=
      fun p hp hp2 => (quotTorsEquiv e' p).1.mp (subsingleton_quot_pH_iff.mp (hdiv p hp hp2))
    have hFtor : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ x : F, p • x = 0 → x = 0 :=
      fun p hp hp2 => (quotTorsEquiv e' p).2.1.mp (subsingleton_torsP_iff.mp (htor p hp hp2))
    have hFa : ∃ a : F, 2 • a = 0 ∧ ∀ b : F, 2 • b ≠ a := by
      obtain ⟨a, ha2, hane⟩ := ha
      refine ⟨e' a, ?_, ?_⟩
      · rw [← map_nsmul]; simp [ha2]
      · intro b hb
        exact hane (e'.symm b) (e'.injective (by rw [map_nsmul, AddEquiv.apply_symm_apply, hb]))
    obtain ⟨E⟩ := finiteZModTwo F hcardF hFdiv hFtor hFa
    exact ⟨e'.trans E⟩

end

end Work.Pi6.EMZ
