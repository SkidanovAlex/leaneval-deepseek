import Mathlib
import Submission.Work.ConCohomology.All
import Submission.Work.ShafarevichKoch.ZModTwoTrivialAction
import Submission.Work.ShafarevichKoch.natCard_ker_H2Res_le_card_Z1

/-!
# `Work.ShafarevichKoch.natCard_ker_H2Res_le_card_invariantHom` -- the **invariant** engine

The counting engine in the form the Shafarevich--Koch route consumes: the kernel of the inflation
`H²(Q,𝔽₂) → H²(G,𝔽₂)` injects into the **`G`-invariant** continuous characters of `N = ker q`,
i.e. into the dual of the *relation-Frattini* quotient `N / N²[N,G]` -- which is exactly the group
bounded by `Work.ShafarevichKoch.InertiaCount` and passed to the limit by
`Work.ShafarevichKoch.natCard_invariantHom_le_of_quotients`.

## Why the invariance is not extra work

The class of a kernel element `y` is represented by a `2`-cocycle `Z y` of `Q` whose pullback to
`G` is a coboundary `d¹(B y)`; the associated `1`-cocycle of `N` is

  `φ_y n = (B y)(i n) + (Z y)(1,1)`.

Its `G`-invariance is a computation with the two cocycle identities: with `X = i n` (`q X = 1`),

  `(B y)(g X g⁻¹) = (B y)(g) + (B y)(X) + (B y)(g⁻¹) - (Z y)(1, q g⁻¹) - (Z y)(q g, q g⁻¹)`
  `(B y)(g) + (B y)(g⁻¹) = (B y)(1) + (Z y)(q g, q g⁻¹)`,  `(B y)(1) = (Z y)(1,1)`,
  `(Z y)(1, a) = (Z y)(1,1)`,

so `(B y)(g X g⁻¹) = (B y)(X)`: **no element of `G` moves `φ_y`**.  (Equivalently, for `N` abelian
this is the classical statement `ker(inf₂) = im(tg)` with `tg` valued in `H¹(N,𝔽₂)^{Q}`.)
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open scoped Classical
open Work.ConCohomology

noncomputable section

namespace Work.ShafarevichKoch

variable {G Q N : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  [Group N] [TopologicalSpace N] [IsTopologicalGroup N]
  [DistribMulAction G (ZMod 2)] [DistribMulAction Q (ZMod 2)] [DistribMulAction N (ZMod 2)]
  [IsDiscreteGModule G (ZMod 2)] [IsDiscreteGModule Q (ZMod 2)] [IsDiscreteGModule N (ZMod 2)]

/-- **The engine with the invariant character group.** -/
theorem natCard_ker_H2Res_le_card_invariantHom (E : GroupExt G Q N) (hq : Continuous E.q)
    (hop : IsOpenMap E.q) (hsurj : Function.Surjective E.q) (hi : Continuous E.i)
    (hcompG : ∀ (g : G) (m : ZMod 2), g • m = E.q g • m)
    (hfin : Finite {φ : N →* Multiplicative (ZMod 2) //
      Continuous (φ : N → Multiplicative (ZMod 2)) ∧ ∀ (g : G) (n : N), φ (E.conj g n) = φ n}) :
    Finite (AddMonoidHom.ker (H2Res E.q hq hcompG)) ∧
      Nat.card (AddMonoidHom.ker (H2Res E.q hq hcompG)) ≤
        Nat.card {φ : N →* Multiplicative (ZMod 2) //
          Continuous (φ : N → Multiplicative (ZMod 2)) ∧
          ∀ (g : G) (n : N), φ (E.conj g n) = φ n} := by
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
  -- the additive function
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
  -- ### the invariance of `φ y`
  -- the two cocycle identities, in the forms used below
  have h_br : ∀ y (p r : G), ((B y) : G → ZMod 2) (p * r)
      = ((B y) : G → ZMod 2) p + ((B y) : G → ZMod 2) r
        - ((Z y).1 : Q × Q → ZMod 2) (E.q p, E.q r) := by
    intro y p r
    have h := hB y p r
    rw [d1Fun_apply, smul_zmodTwo_eq] at h
    rw [h]
    ring
  have h_z1 : ∀ y (r : G), ((Z y).1 : Q × Q → ZMod 2) (1, E.q r)
      = ((Z y).1 : Q × Q → ZMod 2) (1, 1) := by
    intro y r
    have h1 := hB y 1 r
    have h2 := hB y 1 1
    simp only [d1Fun_apply, smul_zmodTwo_eq, map_one, one_mul, mul_one] at h1 h2
    rw [h1, h2]
    ring
  have h6 : ∀ y, ((B y) : G → ZMod 2) 1 = ((Z y).1 : Q × Q → ZMod 2) (1, 1) := by
    intro y
    have h := hB y 1 1
    simp only [d1Fun_apply, smul_zmodTwo_eq, map_one, one_mul, mul_one] at h
    rw [h]
    ring
  have hgg : ∀ y (g : G), ((B y) : G → ZMod 2) g + ((B y) : G → ZMod 2) g⁻¹
      = ((B y) : G → ZMod 2) 1 + ((Z y).1 : Q × Q → ZMod 2) (E.q g, E.q g⁻¹) := by
    intro y g
    have h := h_br y g g⁻¹
    rw [mul_inv_cancel] at h
    rw [h]; ring
  have hinv : ∀ y (g : G) (n : N), φ y (E.conj g n) = φ y n := by
    intro y g n
    have hconj : E.i (E.conj g n) = g * E.i n * g⁻¹ := E.i_conj g n
    have hX : E.q (E.i n) = 1 := q_i E n
    have hq1 : E.q (E.i n * g⁻¹) = E.q g⁻¹ := by rw [map_mul, hX, one_mul]
    have hide : ((B y) : G → ZMod 2) g + ((B y) : G → ZMod 2) g⁻¹
        - ((Z y).1 : Q × Q → ZMod 2) (1, E.q g⁻¹)
        - ((Z y).1 : Q × Q → ZMod 2) (E.q g, E.q g⁻¹) = 0 := by
      rw [hgg y g, h6 y, h_z1 y g⁻¹]
      ring
    have key : ((B y) : G → ZMod 2) (g * E.i n * g⁻¹) = ((B y) : G → ZMod 2) (E.i n) := by
      have h1 := h_br y g (E.i n * g⁻¹)
      have h2 := h_br y (E.i n) g⁻¹
      rw [mul_assoc, h1, h2, hq1, hX]
      have hrearr : ((B y) : G → ZMod 2) g + (((B y) : G → ZMod 2) (E.i n)
            + ((B y) : G → ZMod 2) g⁻¹ - ((Z y).1 : Q × Q → ZMod 2) (1, E.q g⁻¹))
            - ((Z y).1 : Q × Q → ZMod 2) (E.q g, E.q g⁻¹)
            - ((B y) : G → ZMod 2) (E.i n)
          = ((B y) : G → ZMod 2) g + ((B y) : G → ZMod 2) g⁻¹
            - ((Z y).1 : Q × Q → ZMod 2) (1, E.q g⁻¹)
            - ((Z y).1 : Q × Q → ZMod 2) (E.q g, E.q g⁻¹) := by
        abel
      rw [← sub_eq_zero]
      rw [hrearr]
      exact hide
    show ((B y) : G → ZMod 2) (E.i (E.conj g n)) + _ = ((B y) : G → ZMod 2) (E.i n) + _
    rw [hconj, key]
  -- the hom structure
  have hlc' : ∀ y : K, IsLocallyConstant (fun n : N => Multiplicative.ofAdd (φ y n)) := fun y s => by
    show IsOpen ((φ y) ⁻¹' (Multiplicative.ofAdd ⁻¹' s))
    exact hlc y (Multiplicative.ofAdd ⁻¹' s)
  have hcont : ∀ y : K, Continuous (fun n : N => Multiplicative.ofAdd (φ y n)) := fun y =>
    (⟨fun n : N => Multiplicative.ofAdd (φ y n), hlc' y⟩ :
      LocallyConstant N (Multiplicative (ZMod 2))).continuous
  let Ψ : K → {φ : N →* Multiplicative (ZMod 2) //
      Continuous (φ : N → Multiplicative (ZMod 2)) ∧
      ∀ (g : G) (n : N), φ (E.conj g n) = φ n} := fun y =>
    ⟨{ toFun := fun n => Multiplicative.ofAdd (φ y n)
       map_one' := by rw [hone y, ofAdd_zero]
       map_mul' := fun n m => by
         show Multiplicative.ofAdd (φ y (n * m))
           = Multiplicative.ofAdd (φ y n) * Multiplicative.ofAdd (φ y m)
         rw [hadd y n m, ofAdd_add] },
     hcont y,
     fun g n => by
       show Multiplicative.ofAdd (φ y (E.conj g n)) = Multiplicative.ofAdd (φ y n)
       rw [hinv y g n]⟩
  have hΨcoe : ∀ (y : K) (n : N),
      ((Ψ y).1 : N → Multiplicative (ZMod 2)) n = Multiplicative.ofAdd (φ y n) := fun y n => rfl
  have hinj : Function.Injective Ψ := by
    intro y y' hyy'
    have hφ : ∀ n : N, ((B y) : G → ZMod 2) (E.i n) + ((Z y).1 : Q × Q → ZMod 2) (1, 1)
        = ((B y') : G → ZMod 2) (E.i n) + ((Z y').1 : Q × Q → ZMod 2) (1, 1) := by
      intro n
      have h := congrArg (fun (w : {φ : N →* Multiplicative (ZMod 2) //
          Continuous (φ : N → Multiplicative (ZMod 2)) ∧
          ∀ (g : G) (n : N), φ (E.conj g n) = φ n}) =>
            (w.1 : N → Multiplicative (ZMod 2)) n) hyy'
      rw [hΨcoe, hΨcoe] at h
      exact Multiplicative.ofAdd.injective h
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
