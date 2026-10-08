import Mathlib
import Submission.Work.ZASS.Leaf9
import Submission.Work.ZASS.Basic
import Submission.Work.ZASS2.ZassS

/-!
# Area ZASS2: the three-point rule for the coordinate involution `S = zassS C s`

Given field coordinates `C : ZassCoords G X inf zero U` and an involution `s` of `G` that
interchanges `inf` and `zero`, the map `S = zassS C s` on `C.E` is `y ↦` the coordinate of
`s • (point of coordinate y)`.  The *three-point rule* (HB III XI 1.11/1.12, HB p. 179) says
that the Möbius-type map `g = ZassStep S a`, if `g ^ 3` fixes the three points `∞, 0, 1` of the
projective line `ℙ¹(C.E)`, is the identity.

The proof identifies `g` with the action of the group element `x = u₁ · h · s`, where
`τ u₁ = 1` (`u₁ ∈ U` acts as `+1`) and `α h = a²` (`h` in the two-point stabilizer acts as
`× a²`).  The three fixed points of `g³` are then the three fixed points `inf`, `zero` and
`Θ.symm (some 1)` of `x³`; by the `ZassHyps2` clause "every nonidentity element fixes at most
two points" (`Work.ZASS.eq_one_of_fixes_three`) this forces `x³ = 1`, whence `g³ = id`.
-/

namespace Work.ZASS2

open Work.GW2

theorem zassS_three_point {G X : Type} [Group G] [Finite G] [MulAction G X] [Finite X]
    {q : ℕ} (hZ : Work.GW2.ZassHyps2 G X q) {inf zero : X} (hne : inf ≠ zero)
    {U : Subgroup G} (C : Work.GW2.ZassCoords G X inf zero U) {s : G}
    (hs2 : s * s = 1) (hsi : s • inf = zero) (hsz : s • zero = inf)
    (hinv : Work.GW2.Inverts s (Work.Zassenhaus.pairStab G inf zero)) :
    ∀ a : C.E, a ≠ 0 → (Work.GW2.ZassStep (Work.ZASS2.zassS C s) a)^[3] none = none →
      (Work.GW2.ZassStep (Work.ZASS2.zassS C s) a)^[3] (some 0) = some 0 →
      (Work.GW2.ZassStep (Work.ZASS2.zassS C s) a)^[3] (some 1) = some 1 →
      ∀ y, (Work.GW2.ZassStep (Work.ZASS2.zassS C s) a)^[3] y = y := by
  intro a ha h1 h2 h3 y
  classical
  -- the square root `h` of `a ^ 2` in the two-point stabilizer
  have ha2ne : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  obtain ⟨h, hhα⟩ := (C.α_range (a ^ 2) ha2ne).mpr ⟨a, by ring⟩
  -- the unipotent element with `τ u₁ = 1`
  obtain ⟨u₁, hu₁⟩ := C.τ_bij.2 1
  have hhi : ((h : Work.Zassenhaus.pairStab G inf zero) : G) • inf = inf := h.2.2
  set g : G := (u₁ : G) * (h : G) * s with hg
  -- the action of `g = u₁ * h * s` in the affine chart
  have hgz_inf : C.Θ (g • inf) = some 1 := by
    rw [hg, mul_smul, mul_smul, hsi]
    have hh0 : C.Θ ((h : G) • zero) = some 0 := by
      rw [C.scale h zero, C.Θ_zero]
      simp
    rw [C.trans u₁ ((h : G) • zero), hh0, hu₁]
    simp
  have hgz_zero : C.Θ (g • zero) = none := by
    rw [hg, mul_smul, mul_smul, hsz, hhi, C.trans u₁ inf, C.Θ_inf]
    simp
  have hgz_some : ∀ b : C.E, b ≠ 0 →
      C.Θ (g • (C.Θ.symm (some b))) = some (a ^ 2 * zassS C s b + 1) := by
    intro b hb
    rw [hg, mul_smul, mul_smul]
    rw [C.trans u₁ ((h : G) • (s • (C.Θ.symm (some b))))]
    rw [C.scale h (s • (C.Θ.symm (some b)))]
    rw [zassS_spec C hsz hs2 hb, hhα, hu₁]
    simp
  -- `ZassStep (zassS C s) a` is the action of `g`
  have hident : ∀ z : Option C.E,
      ZassStep (zassS C s) a z = C.Θ (g • (C.Θ.symm z)) := by
    intro z
    cases z with
    | none =>
        have hsymm : C.Θ.symm none = inf := (C.Θ.symm_apply_eq).mpr C.Θ_inf.symm
        rw [hsymm, hgz_inf]
        simp [ZassStep, ZassSbar]
    | some b =>
        by_cases hb : b = 0
        · subst hb
          have hsymm : C.Θ.symm (some 0) = zero :=
            (C.Θ.symm_apply_eq).mpr C.Θ_zero.symm
          rw [hsymm, hgz_zero]
          simp [ZassStep, ZassSbar]
        · rw [hgz_some b hb]
          simp [ZassStep, ZassSbar, hb]
  -- iterates of the conjugated action
  have hiter : ∀ (n : ℕ) (z : Option C.E),
      (fun w : Option C.E => C.Θ (g • (C.Θ.symm w)))^[n] z =
        C.Θ (g ^ n • (C.Θ.symm z)) := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ m ih =>
        intro z
        rw [Function.iterate_succ_apply', ih, Equiv.symm_apply_apply, ← mul_smul, ← pow_succ']
  have hpoly : ∀ (n : ℕ) (z : Option C.E),
      (ZassStep (zassS C s) a)^[n] z = C.Θ (g ^ n • (C.Θ.symm z)) := by
    intro n z
    rw [show ZassStep (zassS C s) a = (fun w => C.Θ (g • (C.Θ.symm w))) from funext hident,
      hiter n z]
  -- `g ^ 3` fixes the three points `inf`, `zero`, `Θ.symm (some 1)`
  have hginf : g ^ 3 • inf = inf := by
    have key := h1
    rw [hpoly 3 none, (C.Θ.symm_apply_eq).mpr C.Θ_inf.symm] at key
    exact C.Θ.injective (by rw [key, C.Θ_inf])
  have hgzero : g ^ 3 • zero = zero := by
    have key := h2
    rw [hpoly 3 (some 0), (C.Θ.symm_apply_eq).mpr C.Θ_zero.symm] at key
    exact C.Θ.injective (by rw [key, C.Θ_zero])
  have hgone : g ^ 3 • (C.Θ.symm (some 1)) = C.Θ.symm (some 1) := by
    have key := h3
    rw [hpoly 3 (some 1)] at key
    exact C.Θ.injective (by rw [key, Equiv.apply_symm_apply])
  have hg3 : g ^ 3 = 1 := by
    refine Work.ZASS.eq_one_of_fixes_three hZ hne ?_ ?_ hginf hgzero hgone
    · intro hcon
      have hval : C.Θ inf = C.Θ (C.Θ.symm (some 1)) := congrArg (fun z => C.Θ z) hcon
      rw [C.Θ_inf, Equiv.apply_symm_apply] at hval
      exact absurd hval (by simp)
    · intro hcon
      have hval : C.Θ zero = C.Θ (C.Θ.symm (some 1)) := congrArg (fun z => C.Θ z) hcon
      rw [C.Θ_zero, Equiv.apply_symm_apply] at hval
      exact one_ne_zero (Option.some.inj hval).symm
  rw [hpoly 3 y, hg3, one_smul, Equiv.apply_symm_apply]

end Work.ZASS2
