import Mathlib
import Submission.Work.ConCohomology.All
import Submission.Work.ShafarevichKoch.ZModTwoTrivialAction
import Submission.Work.ShafarevichKoch.natCard_ker_H2Res_le_two_pow

/-!
# `Work.ShafarevichKoch.natCard_ker_H2Res_le_card_Z1` -- the engine without a generation hypothesis

The counting engine `Work.ShafarevichKoch.natCard_ker_H2Res_le_two_pow` bounds
`#ker(H²(Q,𝔽₂) → H²(G,𝔽₂))` by `2^s` **given** a generating set of `s` elements of `N = ker q`.
The present module proves the sharper and hypothesis-free bound

  `#ker(H2Res E.q) ≤ #Z¹(N, 𝔽₂)`,

i.e. the kernel of the inflation injects into the group of continuous crossed homomorphisms
`N → 𝔽₂` (which, for the trivial action, is `Hom_cont(N,𝔽₂)`); the `s`-generator form is then
recovered because `Hom_cont(N,𝔽₂) ↪ (𝔽₂)^s` as soon as `s` elements generate `N`.

The proof is the *tail* of the existing engine: a class `y` in the kernel is represented by a
`2`-cocycle `Z y` whose pullback is the coboundary of some `B y`, and the `1`-cocycle
`φ_y (n) = (B y)(i n) + (Z y)(1,1)` is well defined, additive and locally constant.  The whole
content is that `y ↦ φ_y` is injective: if `φ_y = φ_{y'}`, then `B y - B y'` is constant on
`i(N)`, descends to a locally constant function `W` on `Q` (here `IsOpenMap E.q` is used), and
`d¹W = Z y - Z y'`, so `y = y'`.

The generation hypothesis of the earlier form is used *only* to conclude that `φ_y` is determined
by finitely many of its values; dropping it costs nothing.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Classical
open Work.ConCohomology

noncomputable section

namespace Work.ShafarevichKoch

variable {G Q N : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  [Group N] [TopologicalSpace N] [IsTopologicalGroup N]
  [DistribMulAction G (ZMod 2)] [DistribMulAction Q (ZMod 2)] [DistribMulAction N (ZMod 2)]
  [IsDiscreteGModule G (ZMod 2)] [IsDiscreteGModule Q (ZMod 2)] [IsDiscreteGModule N (ZMod 2)]

/-- **The engine, without a generating set.**  `#ker(inf₂) ≤ #Z¹(N,𝔽₂)`. -/
theorem natCard_ker_H2Res_le_card_Z1 (E : GroupExt G Q N) (hq : Continuous E.q)
    (hop : IsOpenMap E.q) (hsurj : Function.Surjective E.q) (hi : Continuous E.i)
    (hcompG : ∀ (g : G) (m : ZMod 2), g • m = E.q g • m)
    (hfin : Finite (Z1 N (ZMod 2))) :
    Finite (AddMonoidHom.ker (H2Res E.q hq hcompG)) ∧
      Nat.card (AddMonoidHom.ker (H2Res E.q hq hcompG)) ≤ Nat.card (Z1 N (ZMod 2)) := by
  classical
  let K := AddMonoidHom.ker (H2Res E.q hq hcompG)
  let Z : K → Z2 Q (ZMod 2) := fun y =>
    Classical.choose (QuotientAddGroup.mk_surjective y.1)
  have hZ : ∀ y, H2.mk (Z y) = y.1 := fun y =>
    Classical.choose_spec (QuotientAddGroup.mk_surjective y.1)
  have hZk : ∀ y, H2Res E.q hq hcompG (H2.mk (Z y)) = 0 := fun y => by rw [hZ y]; exact y.2
  let B : K → Cochain1 G (ZMod 2) := fun y =>
    Classical.choose (exists_coboundary_of_H2Res_eq_zero E hq hcompG (Z y) (hZk y))
  have hB : ∀ y p r, ((Z y).1 : Q × Q → ZMod 2) (E.q p, E.q r)
      = d1Fun ((B y) : G → ZMod 2) (p, r) := fun y =>
    Classical.choose_spec (exists_coboundary_of_H2Res_eq_zero E hq hcompG (Z y) (hZk y))
  -- the additive, locally constant function attached to a class in the kernel
  let φ : K → N → ZMod 2 := fun y n =>
    ((B y) : G → ZMod 2) (E.i n) + ((Z y).1 : Q × Q → ZMod 2) (1, 1)
  have hadd : ∀ y n m, φ y (n * m) = φ y n + φ y m := fun y n m =>
    add_sum_of_coboundary E (Z y) (B y) (hB y) n m
  have hone : ∀ y, φ y 1 = 0 := by
    intro y
    have h := hadd y 1 1
    rw [mul_one] at h
    have h4 : φ y 1 + φ y 1 = 0 := by
      have h2 : (2 : ZMod 2) = 0 := by decide
      have h3 : (2 : ZMod 2) * φ y 1 = 0 := by rw [h2, zero_mul]
      simpa [two_mul] using h3
    rw [h]
    exact h4
  have hlc : ∀ y, IsLocallyConstant (φ y) := by
    intro y
    have h1 : IsLocallyConstant fun n : N => ((B y) : G → ZMod 2) (E.i n) :=
      ((B y).isLocallyConstant).comp_continuous hi
    have h2 : IsLocallyConstant fun _ : N => ((Z y).1 : Q × Q → ZMod 2) (1, 1) :=
      IsLocallyConstant.const _
    exact h1.add h2
  -- the `1`-cocycle structure
  have hcoc : ∀ y, d1Hom N (ZMod 2) (⟨φ y, hlc y⟩ : Cochain1 N (ZMod 2)) = 0 := by
    intro y
    rw [d1Hom_eq_zero_iff]
    funext p
    obtain ⟨n, m⟩ := p
    show d1Fun (G := N) ((⟨φ y, hlc y⟩ : Cochain1 N (ZMod 2)) : N → ZMod 2) (n, m) = 0
    rw [d1Fun_apply, smul_zmodTwo_eq]
    change φ y m - φ y (n * m) + φ y n = 0
    have h := hadd y n m
    rw [h]
    ring
  let Ψ : K → Z1 N (ZMod 2) := fun y =>
    ⟨(⟨φ y, hlc y⟩ : Cochain1 N (ZMod 2)), hcoc y⟩
  have hΨcoe : ∀ (y : K) (n : N), ((Ψ y).1 : N → ZMod 2) n = φ y n := fun y n => rfl
  have hinj : Function.Injective Ψ := by
    intro y y' hyy'
    have hφ : ∀ n : N, ((B y) : G → ZMod 2) (E.i n) + ((Z y).1 : Q × Q → ZMod 2) (1, 1)
        = ((B y') : G → ZMod 2) (E.i n) + ((Z y').1 : Q × Q → ZMod 2) (1, 1) := by
      intro n
      have h := congrArg (fun (w : Z1 N (ZMod 2)) => ((w.1 : Cochain1 N (ZMod 2)) : N → ZMod 2) n) hyy'
      rw [hΨcoe, hΨcoe] at h
      exact h
    let D : Cochain1 G (ZMod 2) := (B y) - (B y')
    have hDcoe : ∀ g : G, (D : G → ZMod 2) g
        = ((B y) : G → ZMod 2) g - ((B y') : G → ZMod 2) g := fun g => rfl
    have hDconst : ∀ n : N, (D : G → ZMod 2) (E.i n)
        = ((Z y').1 : Q × Q → ZMod 2) (1, 1) - ((Z y).1 : Q × Q → ZMod 2) (1, 1) := by
      intro n
      rw [hDcoe]
      exact i_eq_const E (Z y) (Z y') (B y) (B y') hφ n
    have hDwell : ∀ {p p' : G}, E.q p = E.q p' →
        (D : G → ZMod 2) p = (D : G → ZMod 2) p' := by
      intro p p' hpp'
      rw [hDcoe, hDcoe]
      exact descend_wellDefined E (Z y) (Z y') (B y) (B y') (hB y) (hB y') hDconst hpp'
    let W : Q → ZMod 2 := fun a => (D : G → ZMod 2) (Classical.choose (hsurj a))
    have hWq : ∀ g : G, W (E.q g) = (D : G → ZMod 2) g := fun g =>
      hDwell (Classical.choose_spec (hsurj (E.q g)))
    have hWc : IsLocallyConstant W := by
      apply isLocallyConstant_of_isOpenMap hop hsurj
      rw [show (W ∘ E.q) = (D : G → ZMod 2) from funext hWq]
      exact (D : Cochain1 G (ZMod 2)).isLocallyConstant
    let Wc : Cochain1 Q (ZMod 2) := ⟨W, hWc⟩
    have hdW : (d1Hom Q (ZMod 2) Wc : Cochain2 Q (ZMod 2))
        = ((Z y - Z y' : Z2 Q (ZMod 2)) : Cochain2 Q (ZMod 2)) := by
      ext p
      obtain ⟨a, b⟩ := p
      obtain ⟨p₁, hp₁⟩ := hsurj a
      obtain ⟨p₂, hp₂⟩ := hsurj b
      rw [← hp₁, ← hp₂]
      show d1Fun (G := Q) (Wc : Q → ZMod 2) (E.q p₁, E.q p₂)
        = ((Z y).1 : Q × Q → ZMod 2) (E.q p₁, E.q p₂)
          - ((Z y').1 : Q × Q → ZMod 2) (E.q p₁, E.q p₂)
      rw [hB y p₁ p₂, hB y' p₁ p₂]
      rw [d1Fun_apply, d1Fun_apply, d1Fun_apply]
      change (E.q p₁) • W (E.q p₂) - W (E.q p₁ * E.q p₂) + W (E.q p₁)
        = (p₁ • (B y) p₂ - (B y) (p₁ * p₂) + (B y) p₁)
          - (p₁ • (B y') p₂ - (B y') (p₁ * p₂) + (B y') p₁)
      rw [← map_mul, hWq (p₁ * p₂), hWq p₂, hWq p₁]
      simp only [smul_zmodTwo_eq]
      rw [hDcoe p₂, hDcoe (p₁ * p₂), hDcoe p₁]
      abel
    have hB2 : (Z y - Z y' : Z2 Q (ZMod 2)) ∈ B2' Q (ZMod 2) := by
      rw [mem_B2', mem_B2]
      exact ⟨Wc, hdW⟩
    have hmk : H2.mk (Z y) = H2.mk (Z y') := by
      rw [H2.mk_eq_mk_iff]
      exact hB2
    exact Subtype.ext (by rw [← hZ y, ← hZ y', hmk])
  exact ⟨Finite.of_injective Ψ hinj, Nat.card_le_card_of_injective Ψ hinj⟩

end Work.ShafarevichKoch
