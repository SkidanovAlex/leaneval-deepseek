import Mathlib
import Submission.Work.BG.Thm43Defs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.H0Conj
import Submission.Work.BG.sec2CtxOfBGData
import Submission.Work.BG.kappaExists
import Submission.Work.BG.nOrbBInv
import Submission.Work.BG.nOrbCosets

/-!
# Area BG: `NOrbProp` (`N_G(S)`-orbits on `Irr(B)`)

This file proves `Work.GW2.C23.NOrbProp`: for Bender–Glauberman data `D` with `D.n = 2` (so
that `S ≅ V₄` is a Klein four group), every `N_G(S)`-orbit on the class functions of `B` has
one or three elements; a non-`N_G(S)`-fixed `θ` therefore has exactly three pairwise distinct
conjugates.

The group-theoretic input is

* `B` is normalized by `N_G(S)`, and every element of `C_G(S)` acts on `B` as an *inner*
  automorphism of `B`.  Consequently `C_G(S)` acts trivially on the class functions of `B`;
* `N_G(S)` is covered by the three cosets `C_G(S)`, `xC_G(S)`, `x²C_G(S)` for any
  `x ∈ N_G(S) ∖ C_G(S)`, and the cube of every element of `N_G(S)` lies in `C_G(S)`.

These are `Work.BG.nOrbBInv` and `Work.BG.nOrbCosets` (files `BG/nOrbBInv.lean` and
`BG/nOrbCosets.lean`).  What this file does is the character-theoretic part: the conjugation
action `θ ↦ θˣ` on `ClassFunction ↥B ℂ`, its calculus, and the orbit argument.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.GW2.C23

variable {G : Type} [Group G] [Finite G]

/-! ## The conjugation action on class functions of `B` -/

/-- Conjugation by `x` as an endomorphism of `B`, for an `x` normalizing `B`. -/
noncomputable def conjHom (D : BGData G) (x : G) (hx : ∀ b ∈ D.B, x⁻¹ * b * x ∈ D.B) :
    ↥D.B →* ↥D.B where
  toFun b := ⟨x⁻¹ * (b : G) * x, hx b b.2⟩
  map_one' := by ext; simp
  map_mul' a b := by
    ext
    simp only [Subgroup.coe_mul]
    group

@[simp]
theorem conjHom_apply (D : BGData G) (x : G) (hx : ∀ b ∈ D.B, x⁻¹ * b * x ∈ D.B)
    (b : ↥D.B) : conjHom D x hx b = ⟨x⁻¹ * (b : G) * x, hx b b.2⟩ := rfl

/-- `θˣ`, the `x`-conjugate of a class function on `B` (`(θˣ)(b) = θ(x⁻¹ b x)`), for an `x`
normalizing `B`. -/
noncomputable def conjCF (D : BGData G) (x : G) (hx : ∀ b ∈ D.B, x⁻¹ * b * x ∈ D.B)
    (θ : ClassFunction ↥D.B ℂ) : ClassFunction ↥D.B ℂ :=
  ClassFunction.compHom (conjHom D x hx) θ

@[simp]
theorem conjCF_apply (D : BGData G) (x : G) (hx : ∀ b ∈ D.B, x⁻¹ * b * x ∈ D.B)
    (θ : ClassFunction ↥D.B ℂ) (b : ↥D.B) :
    conjCF D x hx θ b = θ ⟨x⁻¹ * (b : G) * x, hx b b.2⟩ := rfl

/-- `conjCF` only depends on the conjugating element, not on the proof that it normalizes `B`. -/
theorem conjCF_congr (D : BGData G) (x : G)
    (hx hx' : ∀ b ∈ D.B, x⁻¹ * b * x ∈ D.B) (θ : ClassFunction ↥D.B ℂ) :
    conjCF D x hx θ = conjCF D x hx' θ := by
  ext b
  simp only [conjCF_apply]

/-- `conjCF` is insensitive to replacing the conjugating element by an equal one. -/
theorem conjCF_congr_arg (D : BGData G) {x y : G} (hxy : x = y)
    (hx : ∀ b ∈ D.B, x⁻¹ * b * x ∈ D.B) (hy : ∀ b ∈ D.B, y⁻¹ * b * y ∈ D.B)
    (θ : ClassFunction ↥D.B ℂ) : conjCF D x hx θ = conjCF D y hy θ := by
  subst hxy
  exact conjCF_congr D x hx hy θ

/-- The conjugation action is contravariantly multiplicative: `(θˣ)ʸ = θʸˣ`. -/
theorem conjCF_comp (D : BGData G) (x y : G)
    (hy : ∀ b ∈ D.B, y⁻¹ * b * y ∈ D.B) (hx : ∀ b ∈ D.B, x⁻¹ * b * x ∈ D.B)
    (hyx : ∀ b ∈ D.B, (y * x)⁻¹ * b * (y * x) ∈ D.B) (θ : ClassFunction ↥D.B ℂ) :
    conjCF D y hy (conjCF D x hx θ) = conjCF D (y * x) hyx θ := by
  ext b
  simp only [conjCF_apply]
  refine congrArg θ (Subtype.ext ?_)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

/-- `ConjBy` holds for the class function constructed by `conjCF`. -/
theorem conjBy_conjCF (D : BGData G) (x : G) (hx : ∀ b ∈ D.B, x⁻¹ * b * x ∈ D.B)
    (θ : ClassFunction ↥D.B ℂ) : ConjBy D x θ (conjCF D x hx θ) := by
  intro b b' hb'
  have hbb : (⟨x⁻¹ * (b : G) * x, hx b b.2⟩ : ↥D.B) = b' := Subtype.ext hb'.symm
  rw [conjCF_apply, hbb]

/-- Uniqueness: `ConjBy D x θ θ'` determines `θ'`. -/
theorem eq_conjCF_of_conjBy (D : BGData G) (x : G) (hx : ∀ b ∈ D.B, x⁻¹ * b * x ∈ D.B)
    (θ : ClassFunction ↥D.B ℂ) {θ' : ClassFunction ↥D.B ℂ} (h : ConjBy D x θ θ') :
    θ' = conjCF D x hx θ := by
  ext b
  rw [conjCF_apply]
  exact (h b ⟨x⁻¹ * (b : G) * x, hx b b.2⟩ rfl)

/-! ## `NOrbProp` -/

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C23 in
theorem nOrb {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) : Work.GW2.C23.NOrbProp D := by
  intro hn θ hnf
  -- group-theoretic input: `B` is `N_G(S)`-invariant and `C_G(S)` acts on `B` by inner
  -- automorphisms (`Work.BG.nOrbBInv`), and `N_G(S)` is covered by the three cosets
  -- `C_G(S)`, `xC_G(S)`, `x²C_G(S)` (`Work.BG.nOrbCosets`).
  obtain ⟨hBinv, hInner⟩ := nOrbBInv D hn
  obtain ⟨hCube, hCover⟩ := nOrbCosets D hn
  set C : Subgroup G := Subgroup.centralizer ((D.S : Subgroup G) : Set G) with hCdef
  set N : Subgroup G := Subgroup.normalizer ((D.S : Subgroup G) : Set G) with hNdef
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer ((D.S : Subgroup G) : Set G)
  -- (1) an element `x ∈ N` at which `θ` is not fixed
  have hnf' : ∃ x ∈ N, ¬ ConjBy D x θ θ := by
    by_contra h
    refine hnf fun x hx => ?_
    by_contra hconj
    exact h ⟨x, hx, hconj⟩
  obtain ⟨x, hxN, hxnot⟩ := hnf'
  -- (2) elements of `C` act trivially on class functions of `B`
  have hfixC : ∀ (c : G) (hc : c ∈ C) (hcN : c ∈ N) (φ : ClassFunction ↥D.B ℂ),
      conjCF D c (hBinv c hcN) φ = φ := by
    intro c hc hcN φ
    ext b
    simp only [conjCF_apply]
    obtain ⟨b₀, hb₀, hconj⟩ := hInner c hc b b.2
    have hE : (⟨c⁻¹ * (b : G) * c, hBinv c hcN b b.2⟩ : ↥D.B) =
        (⟨b₀, hb₀⟩ : ↥D.B) * b * ((⟨b₀, hb₀⟩ : ↥D.B))⁻¹ :=
      Subtype.ext (by simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hconj)
    rw [hE]
    exact φ.conj_eq b ⟨b₀, hb₀⟩
  have hxnotC : x ∉ C := by
    intro hxC
    refine hxnot ?_
    have h := conjBy_conjCF D x (hBinv x hxN) θ
    rwa [hfixC x hxC hxN θ] at h
  -- (3) the three conjugates
  have hxxN : x * x ∈ N := N.mul_mem hxN hxN
  have hxxxN : x * (x * x) ∈ N := N.mul_mem hxN hxxN
  have hcomp : ∀ (y z : G) (hy : y ∈ N) (hz : z ∈ N) (φ : ClassFunction ↥D.B ℂ),
      conjCF D y (hBinv y hy) (conjCF D z (hBinv z hz) φ)
        = conjCF D (y * z) (hBinv (y * z) (N.mul_mem hy hz)) φ :=
    fun y z hy hz φ =>
      conjCF_comp D z y (hBinv y hy) (hBinv z hz) (hBinv (y * z) (N.mul_mem hy hz)) φ
  have hx3eq : x ^ 3 = x * (x * x) := by
    show x ^ (2 + 1) = x * (x * x)
    rw [pow_succ', pow_two]
  have hx3C : x * (x * x) ∈ C := by
    have h := hCube x hxN
    rwa [hx3eq] at h
  have hcube : conjCF D (x * (x * x)) (hBinv (x * (x * x)) hxxxN) θ = θ :=
    hfixC (x * (x * x)) hx3C hxxxN θ
  have hθx : conjCF D x (hBinv x hxN) θ ≠ θ := by
    intro h
    refine hxnot ?_
    have hh := conjBy_conjCF D x (hBinv x hxN) θ
    rwa [h] at hh
  have hθxx : conjCF D (x * x) (hBinv (x * x) hxxN) θ ≠ θ := by
    intro h
    have hA : conjCF D x (hBinv x hxN) (conjCF D (x * x) (hBinv (x * x) hxxN) θ)
        = conjCF D x (hBinv x hxN) θ := by rw [h]
    rw [hcomp x (x * x) hxN hxxN θ] at hA
    exact hθx (hA.symm.trans hcube)
  have hθxx' : conjCF D (x * x) (hBinv (x * x) hxxN) θ ≠ conjCF D x (hBinv x hxN) θ := by
    intro h
    have hA : conjCF D x (hBinv x hxN) (conjCF D (x * x) (hBinv (x * x) hxxN) θ)
        = conjCF D x (hBinv x hxN) (conjCF D x (hBinv x hxN) θ) := by rw [h]
    rw [hcomp x (x * x) hxN hxxN θ, hcomp x x hxN hxN θ] at hA
    rw [hcube] at hA
    exact hθxx hA.symm
  -- (4) assembly
  refine ⟨conjCF D x (hBinv x hxN) θ, conjCF D (x * x) (hBinv (x * x) hxxN) θ,
    ⟨x, hxN, conjBy_conjCF D x (hBinv x hxN) θ⟩,
    ⟨x * x, hxxN, conjBy_conjCF D (x * x) (hBinv (x * x) hxxN) θ⟩,
    hθx.symm, hθxx.symm, hθxx'.symm, ?_⟩
  intro θ' hθ'
  obtain ⟨y, hyN, hyc⟩ := hθ'
  have hyeq : θ' = conjCF D y (hBinv y hyN) θ := eq_conjCF_of_conjBy D y (hBinv y hyN) θ hyc
  rcases hCover x hxN hxnotC y hyN with hyC | ⟨c, hc, hycx⟩ | ⟨c, hc, hycx⟩
  · exact Or.inl (hyeq.trans (hfixC y hyC hyN θ))
  · refine Or.inr (Or.inl ?_)
    refine hyeq.trans ?_
    calc conjCF D y (hBinv y hyN) θ
        = conjCF D (c * x) (hBinv (c * x) (N.mul_mem (hCN hc) hxN)) θ :=
          conjCF_congr_arg D hycx (hBinv y hyN) (hBinv (c * x) (N.mul_mem (hCN hc) hxN)) θ
      _ = conjCF D c (hBinv c (hCN hc)) (conjCF D x (hBinv x hxN) θ) :=
          (hcomp c x (hCN hc) hxN θ).symm
      _ = conjCF D x (hBinv x hxN) θ := hfixC c hc (hCN hc) (conjCF D x (hBinv x hxN) θ)
  · refine Or.inr (Or.inr ?_)
    have hyN' : c * x ^ 2 ∈ N := hycx ▸ hyN
    refine hyeq.trans ?_
    calc conjCF D y (hBinv y hyN) θ
        = conjCF D (c * x ^ 2) (hBinv (c * x ^ 2) hyN') θ :=
          conjCF_congr_arg D hycx (hBinv y hyN) (hBinv (c * x ^ 2) hyN') θ
      _ = conjCF D (c * (x * x)) (hBinv (c * (x * x)) (N.mul_mem (hCN hc) hxxN)) θ :=
          conjCF_congr_arg D (by rw [pow_two]) (hBinv (c * x ^ 2) hyN')
            (hBinv (c * (x * x)) (N.mul_mem (hCN hc) hxxN)) θ
      _ = conjCF D c (hBinv c (hCN hc)) (conjCF D (x * x) (hBinv (x * x) hxxN) θ) :=
          (hcomp c (x * x) (hCN hc) hxxN θ).symm
      _ = conjCF D (x * x) (hBinv (x * x) hxxN) θ :=
          hfixC c hc (hCN hc) (conjCF D (x * x) (hBinv (x * x) hxxN) θ)

end Work.BG
