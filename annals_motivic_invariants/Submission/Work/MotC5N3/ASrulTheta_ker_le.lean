import Mathlib
import Submission.Work.MotC5N3.ASRulingMainV2Gen
import Submission.Work.MotC5N3.hparam_kernel
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.CensusAS2
import Submission.Work.MotAS.ASRulingMain
import Submission.Work.MotAS.ASRulingMainAux
import Submission.Work.MotAS.AmatAS2_ker_iff
import Submission.Work.MotAS.ASRul.kernel_basis
import Submission.Work.MotAS.KleinTwScalarASv
import Submission.Work.MotAS.ASChart2Defs
import Submission.Work.MotAS.ASChartGeo
import Submission.Work.MotA.coheight_eq_one_iff
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.MotC5N3

open MvPolynomial

/-! ## Naturality of the AS ruling vectors under `MvPolynomial.map` -/

theorem map_kbRv {K L : Type} [Field K] [Field L] (φ : K →+* L) (a b g : K) (i : Fin 5) :
    MvPolynomial.map φ (Work.MotAS.ASRul.kbRv a b g i)
      = Work.MotAS.ASRul.kbRv (φ a) (φ b) (φ g) i := by
  fin_cases i <;>
    (simp only [Work.MotAS.ASRul.kbRv, Matrix.cons_val_zero', Matrix.cons_val_succ',
        map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_zero, map_one,
        MvPolynomial.map_C, MvPolynomial.map_X] <;>
      try ring)

theorem map_kbRw {K L : Type} [Field K] [Field L] (φ : K →+* L) (a b g : K) (i : Fin 5) :
    MvPolynomial.map φ (Work.MotAS.ASRul.kbRw a b g i)
      = Work.MotAS.ASRul.kbRw (φ a) (φ b) (φ g) i := by
  fin_cases i <;>
    (simp only [Work.MotAS.ASRul.kbRw, Matrix.cons_val_zero', Matrix.cons_val_succ',
        map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_zero, map_one,
        MvPolynomial.map_C, MvPolynomial.map_X] <;>
      try ring)

/-- **The kernel of the AS ruling presentation is contained in every height-one prime at which the
source ruling quintic `sAS2` vanishes and at which `fwVecAS2 · 0` and `fwVecAS2 · 3` do not.**

Route (Step 3 of the K5 assembly, `MOTIVIC_CHAR5_N3_LEAD.md` §3): let `k'` be the residue field of
`x`, `f : K[X₀,X₁,X₂] → k'` the residue map (with `ker f = x.asIdeal`), `y := f ∘ ASrulYv` the
source stereographic point and `c' := f ∘ fwVecAS2 a b g` its image under `kleinPAS`.  The link
identity `I1^AS` together with `sAS2 ∈ x` shows `kleinRAS c' = 0`, so the base point
`(b₁,b₂,b₃) := (c'₁/c'₀, c'₂/c'₀, c'₃/c'₀)` lies on the residual curve; `hparam_kernel` then
describes the chart coordinates of `y` in terms of the ruling vectors evaluated at `(b₁,b₂,b₃)`.

On the other side, the evaluation `ev` at `(b₁,b₂,b₃)` kills `√(ZIAS a b g)` (because the base point
lies on the residual curve), hence descends to a `K`-algebra map `ψ : A → k'`; extending it to
`σ₀ : A[T] → k'` by `T ↦ (a+2b)·y₃/y₄` and localising at `ε` gives `σ : A[T][1/ε] → k'` with
`σ (ASrulTheta (X j)) = f (X j)` for all `j`.  Then `σ ∘ θ = f`, whence `θ p = 0 ⟹ f p = 0 ⟹
p ∈ x.asIdeal`.

The lemma is stated for an *abstract* residue field `k'` carrying an explicit `K`-algebra structure
with `IsFractionRing (K[X] ⧸ x) k'`.  Keeping `k'` abstract makes its instance arguments unique in
the proof (`FractionRing = Localization = OreLocalization` carries several `CommSemiring`
instances, see `NOTE_STRulingDiv2.md`); the corollary `ASrulTheta_ker_le` below instantiates it at
the concrete residue field `resF K x`. -/
theorem ASrulTheta_ker_le_aux (K : Type) [Field K] [CharP K 5] (a b g : K)
    (hDZ : IsDomain (Work.MotC5N3.ASrulA a b g)) (hε : Work.MotC5N3.ASrulEpsA a b g ≠ 0)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hab : a * b ≠ 0) (hg : ¬ ∃ c : K, c ^ 5 - c = g)
    (x : Work.MotA.polySpec K 3) (hcoh : Order.coheight x = 1)
    (hx : Work.MotAS.sAS2 a b g ∈ x.asIdeal)
    (hfw : Work.MotAS.fwVecAS2 a b g 0 ∉ x.asIdeal)
    (h3 : Work.MotAS.fwVecAS2 a b g 3 ∉ x.asIdeal)
    (k' : Type) [Field k'] [Algebra K k']
    [Algebra (MvPolynomial (Fin 3) K ⧸ x.asIdeal) k']
    [IsScalarTower K (MvPolynomial (Fin 3) K ⧸ x.asIdeal) k']
    [IsFractionRing (MvPolynomial (Fin 3) K ⧸ x.asIdeal) k']
    (hmap_inj : Function.Injective (algebraMap K k')) :
    RingHom.ker (Work.MotC5N3.ASrulTheta a b g hDZ) ≤ x.asIdeal := by
  -- pin the instances of the quotient `A = K[X] ⧸ √ZIAS` (the `Ideal.Quotient.semiring` /
  -- `CommSemiring.toSemiring` diamond), as in `Work.MotAS.ASRulConstDefs`; without this the
  -- instance search for `Algebra A[T] A[T][1/ε]` is stuck.
  letI : Semiring (Work.MotC5N3.ASrulA a b g) :=
    (inferInstance : CommSemiring (Work.MotC5N3.ASrulA a b g)).toSemiring
  letI : CommSemiring (Work.MotC5N3.ASrulA a b g) := inferInstance
  letI : CommRing (Work.MotC5N3.ASrulA a b g) := inferInstance
  letI : Algebra (Polynomial (Work.MotC5N3.ASrulA a b g))
      (Localization.Away (Polynomial.C (Work.MotC5N3.ASrulEpsA a b g))) := inferInstance
  haveI hxprime : x.asIdeal.IsPrime := x.isPrime
  let q := MvPolynomial (Fin 3) K ⧸ x.asIdeal
  have h5K : (5 : K) = 0 := CharP.cast_eq_zero K 5
  haveI hchar : CharP k' 5 := charP_of_injective_algebraMap hmap_inj 5
  have h5k : (5 : k') = 0 := CharP.cast_eq_zero k' 5
  -- ## 1.  The residue map `f : K[X] → k'` and its kernel
  let loc : MvPolynomial (Fin 3) K →+* k' := (algebraMap q k').comp (Ideal.Quotient.mk x.asIdeal)
  let f : MvPolynomial (Fin 3) K → k' := ⇑loc
  have hfC : ∀ c : K, loc (MvPolynomial.C c) = algebraMap K k' c := by
    intro c
    show algebraMap q k' (Ideal.Quotient.mk x.asIdeal (MvPolynomial.C c)) = algebraMap K k' c
    rw [← MvPolynomial.algebraMap_eq]
    rw [Ideal.Quotient.mk_algebraMap, ← IsScalarTower.algebraMap_apply K q k']
  have hfk : ∀ p : MvPolynomial (Fin 3) K, f p = 0 ↔ p ∈ x.asIdeal := by
    intro p
    show algebraMap q k' (Ideal.Quotient.mk x.asIdeal p) = 0 ↔ p ∈ x.asIdeal
    constructor
    · intro h
      have h' : Ideal.Quotient.mk x.asIdeal p = 0 :=
        IsFractionRing.injective q k' (by rw [h, map_zero])
      exact Ideal.Quotient.eq_zero_iff_mem.mp h'
    · intro hp
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
  have hker : RingHom.ker loc = x.asIdeal := by
    ext p
    rw [RingHom.mem_ker]
    exact hfk p
  -- ## 2.  Denominators
  have ha0 : a ≠ 0 := fun h => hab (by rw [h, zero_mul])
  have hb0 : b ≠ 0 := fun h => hab (by rw [h, mul_zero])
  have hg0 : g ≠ 0 := fun h => hg ⟨0, by rw [h]; ring⟩
  have hA : 2 * a - b ≠ 0 := by
    intro h
    exact ha (by linear_combination (3 * a + b) * h - a ^ 2 * h5K)
  have hB : a + 2 * b ≠ 0 := by
    intro h
    exact ha (by linear_combination (a + 2 * b) * h - (a * b + b ^ 2) * h5K)
  -- ## 3.  The base-field elements in `k'`
  let a' : k' := algebraMap K k' a
  let b' : k' := algebraMap K k' b
  let g' : k' := algebraMap K k' g
  have hconst : ∀ c : K, c ≠ 0 → loc (MvPolynomial.C c) ≠ 0 := by
    intro c hc h0
    have h2 : MvPolynomial.C c ∈ x.asIdeal := (hfk _).mp h0
    have h3 : (1 : MvPolynomial (Fin 3) K) ∈ x.asIdeal := by
      have h4 := x.asIdeal.mul_mem_right (MvPolynomial.C c⁻¹) h2
      rw [← map_mul, mul_inv_cancel₀ hc, map_one] at h4
      exact h4
    exact hxprime.ne_top (Ideal.eq_top_iff_one x.asIdeal |>.mpr h3)
  have h2K : (2 : K) ≠ 0 := by
    intro h
    have hh : (5 : K) = 2 * 2 + 1 := by norm_num
    rw [h, mul_zero, zero_add] at hh
    rw [h5K] at hh
    exact one_ne_zero hh.symm
  have ha' : a' ≠ 0 := by
    rw [show a' = loc (MvPolynomial.C a) from (hfC a).symm]
    exact hconst a ha0
  have hb' : b' ≠ 0 := by
    rw [show b' = loc (MvPolynomial.C b) from (hfC b).symm]
    exact hconst b hb0
  have hg' : g' ≠ 0 := by
    rw [show g' = loc (MvPolynomial.C g) from (hfC g).symm]
    exact hconst g hg0
  have hA' : 2 * a' - b' ≠ 0 := by
    have h1 : 2 * a' - b' = loc (MvPolynomial.C (2 * a - b)) := by
      rw [show a' = loc (MvPolynomial.C a) from (hfC a).symm,
          show b' = loc (MvPolynomial.C b) from (hfC b).symm]
      rw [show (MvPolynomial.C (2 * a - b) : MvPolynomial (Fin 3) K)
          = 2 * MvPolynomial.C a - MvPolynomial.C b from by
        simp only [map_sub, map_mul, map_ofNat]]
      simp only [map_sub, map_mul, map_ofNat]
    rw [h1]
    exact hconst (2 * a - b) hA
  have hB' : a' + 2 * b' ≠ 0 := by
    have h1 : a' + 2 * b' = loc (MvPolynomial.C (a + 2 * b)) := by
      rw [show a' = loc (MvPolynomial.C a) from (hfC a).symm,
          show b' = loc (MvPolynomial.C b) from (hfC b).symm]
      rw [show (MvPolynomial.C (a + 2 * b) : MvPolynomial (Fin 3) K)
          = MvPolynomial.C a + 2 * MvPolynomial.C b from by
        simp only [map_add, map_mul, map_ofNat]]
      simp only [map_add, map_mul, map_ofNat]
    rw [h1]
    exact hconst (a + 2 * b) hB
  have hb2a : b' ≠ 2 * a' := fun h => hA' (by rw [h]; ring)
  -- ## 4.  The source stereographic point `y` and its image `c`
  let y : Fin 5 → k' := fun i => f (Work.MotAS.ASrulYv K a b i)
  let c : Fin 5 → k' := fun i => f (Work.MotAS.fwVecAS2 a b g i)
  have hc0 : c 0 ≠ 0 := by
    intro h
    refine hfw ?_
    rw [← hker]
    exact RingHom.mem_ker.mpr h
  have hc3 : c 3 ≠ 0 := by
    intro h
    refine h3 ?_
    rw [← hker]
    exact RingHom.mem_ker.mpr h
  have hc4 : c 4 = 0 := by
    change loc (Work.MotAS.fwVecAS2 a b g 4) = 0
    rw [Work.MotAS.fwVecAS2_four_zero, map_zero]
  have hy4 : y 4 ≠ 0 := by
    change loc (Work.MotAS.ASrulYv K a b 4) ≠ 0
    rw [Work.MotAS.ASrulYv_four]
    exact hconst (2 * (a ^ 2 - a * b - b ^ 2)) (mul_ne_zero h2K ha)
  have hchart : ∀ j : Fin 3, y (Work.MotAS.asCh3 j) = y 4 * f (MvPolynomial.X j) := by
    intro j
    have h := congrArg (fun z : MvPolynomial (Fin 3) K => loc z)
      (Work.MotAS.ASrulYv_ch3 K a b j)
    rw [map_mul] at h
    simpa only [y] using h
  -- ## 5.  The link identity applied to `y`
  have hyPAS : Work.MotAS.kleinPAS a' b' g' y = c := by
    have h := Work.MotAS.KleinTwScalarAS_map_kleinPAS loc (MvPolynomial.C a) (MvPolynomial.C b)
      (MvPolynomial.C g) (Work.MotAS.ASrulYv K a b)
    simp only [hfC] at h
    simpa only [y, c, Work.MotAS.fwVecAS2, Work.MotAS.ASrulYv] using h
  have hySec : Work.MotAS.kleinSecAS a' b' g' y = 0 := by
    have h := Work.MotAS.KleinTwScalarAS_map_kleinSecAS loc (MvPolynomial.C a) (MvPolynomial.C b)
      (MvPolynomial.C g) (Work.MotAS.ASrulYv K a b)
    simp only [hfC] at h
    have hs : f (Work.MotAS.sAS2 a b g) = 0 :=
      RingHom.mem_ker.mp (by rw [hker]; exact hx)
    have h' : Work.MotAS.kleinSecAS a' b' g' y = f (Work.MotAS.sAS2 a b g) := by
      simpa only [y, Work.MotAS.sAS2, Work.MotAS.ASrulYv] using h
    rw [h', hs]
  have hkleinRAS : Work.MotAS.kleinRAS a' b' g' c = 0 := by
    have hI1 := Work.MotAS.KleinTwScalarASv a' b' g' y h5k
    rw [hyPAS] at hI1
    rw [hI1, hySec]
    funext i; simp
  have hklein' : Work.MotAS.kleinRAS a' b' g' ![c 0, c 1, c 2, c 3, 0] = 0 := by
    have hcc : (fun i => c i) = ![c 0, c 1, c 2, c 3, 0] := by
      funext i; fin_cases i <;> simp [hc4]
    rw [← hcc]
    exact hkleinRAS
  -- ## 6.  The base point, the evaluation `ev`, and `hparam_kernel`
  let b₁ : k' := c 1 / c 0
  let b₂ : k' := c 2 / c 0
  let b₃ : k' := c 3 / c 0
  have hb₃ : b₃ ≠ 0 := div_ne_zero hc3 hc0
  let ev : MvPolynomial (Fin 3) K →ₐ[K] k' := MvPolynomial.aeval ![b₁, b₂, b₃]
  have hbase : ∀ j : Fin 5, MvPolynomial.eval ![b₁, b₂, b₃]
      (Work.MotAS.zcubAS a' b' g' j) = 0 := by
    intro j
    have h := Work.MotAS.zcubAS_eval_eq a' b' g' b₁ b₂ b₃ j
    rw [h]
    simpa using congrFun (Work.MotAS.kleinRAS_chart_eq_zero a' b' g'
      (c 0) (c 1) (c 2) (c 3) hc0 hklein') j
  have hkerAmat : Matrix.mulVec (Work.MotAS.AmatAS2 a' b' g' ![1, b₁, b₂, b₃, 0]) y = 0 := by
    have h2 : Matrix.mulVec (Work.MotAS.AmatAS2 a' b' g' c) y = 0 := by
      rw [← hyPAS]
      exact Work.MotAS.AmatAS2_mulVec_of_kleinPAS a' b' g' h5k y
    have hcs : c = c 0 • ![1, b₁, b₂, b₃, 0] := by
      funext i
      fin_cases i
      · show c 0 = c 0 * 1
        rw [mul_one]
      · show c 1 = c 0 * b₁
        rw [show b₁ = c 1 / c 0 from rfl]
        exact (mul_div_cancel₀ (c 1) hc0).symm
      · show c 2 = c 0 * b₂
        rw [show b₂ = c 2 / c 0 from rfl]
        exact (mul_div_cancel₀ (c 2) hc0).symm
      · show c 3 = c 0 * b₃
        rw [show b₃ = c 3 / c 0 from rfl]
        exact (mul_div_cancel₀ (c 3) hc0).symm
      · show c 4 = c 0 * 0
        rw [hc4, mul_zero]
    rw [hcs, Work.MotAS.AmatAS2_mulVec_smul] at h2
    rcases smul_eq_zero.mp h2 with h4 | h4
    · exact absurd h4 hc0
    · exact h4
  have hparam := hparam_kernel a' b' g' b₁ b₂ b₃ y ha' hb' hb2a hg' hb₃ hy4 hbase hkerAmat
  -- ## 7.  The evaluated ruling vectors (over `k'`)
  have hevR : ∀ i : Fin 5, ev (Work.MotAS.ASRul.kbRv a b g i)
      = MvPolynomial.eval ![b₁, b₂, b₃] (Work.MotAS.ASRul.kbRv a' b' g' i) := by
    intro i
    change MvPolynomial.aeval ![b₁, b₂, b₃] (Work.MotAS.ASRul.kbRv a b g i)
      = MvPolynomial.eval ![b₁, b₂, b₃] (Work.MotAS.ASRul.kbRv a' b' g' i)
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map,
      map_kbRv (K := K) (L := k') (algebraMap K k') a b g i]
  have hevW : ∀ i : Fin 5, ev (Work.MotAS.ASRul.kbRw a b g i)
      = MvPolynomial.eval ![b₁, b₂, b₃] (Work.MotAS.ASRul.kbRw a' b' g' i) := by
    intro i
    change MvPolynomial.aeval ![b₁, b₂, b₃] (Work.MotAS.ASRul.kbRw a b g i)
      = MvPolynomial.eval ![b₁, b₂, b₃] (Work.MotAS.ASRul.kbRw a' b' g' i)
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map,
      map_kbRw (K := K) (L := k') (algebraMap K k') a b g i]
  have hevR3 : ev (Work.MotAS.ASRul.kbRv a b g 3) = (2 * a' - b') * (a' + 2 * b') * b₃ ^ 2 := by
    rw [hevR 3, Work.MotAS.eval_kbRv_three]
  have hevR3ne : ev (Work.MotAS.ASRul.kbRv a b g 3) ≠ 0 := by
    rw [hevR3]
    exact mul_ne_zero (mul_ne_zero hA' hB') (pow_ne_zero 2 hb₃)
  have hevW4 : ev (Work.MotAS.ASRul.kbRw a b g 4)
      = (a' + 2 * b') * ev (Work.MotAS.ASRul.kbRv a b g 3) := by
    rw [hevR3, hevW 4, Work.MotAS.eval_kbRw_four]
    first | refl_ring1 | ring
  have hevW4ne : ev (Work.MotAS.ASRul.kbRw a b g 4) ≠ 0 := by
    rw [hevW4]
    exact mul_ne_zero hB' hevR3ne
  -- ## 8.  The evaluation kills the residual-curve ideal, hence descends to `A`
  have hbZ : ∀ j : Fin 5, ev (Work.MotAS.zcubAS a b g j) = 0 := by
    intro j
    have hwv : (fun i : Fin 5 => ev (![1, MvPolynomial.X 0, MvPolynomial.X 1,
        MvPolynomial.X 2, 0] i)) = ![1, b₁, b₂, b₃, 0] := by
      funext i
      fin_cases i <;> simp [ev, MvPolynomial.aeval_X]
    have hca : ev (MvPolynomial.C a) = a' := AlgHom.commutes ev a
    have hcb : ev (MvPolynomial.C b) = b' := AlgHom.commutes ev b
    have hcg : ev (MvPolynomial.C g) = g' := AlgHom.commutes ev g
    have hnat := congrFun (Work.MotAS.KleinTwScalarAS_map_kleinRAS
      (A := MvPolynomial (Fin 3) K) (B := k') (ev : MvPolynomial (Fin 3) K →+* k')
      (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
      (![1, MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, 0] :
        Fin 5 → MvPolynomial (Fin 3) K)) j
    rw [show Work.MotAS.zcubAS a b g j = Work.MotAS.kleinRAS (MvPolynomial.C a)
        (MvPolynomial.C b) (MvPolynomial.C g)
        ![1, MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, 0] j from rfl]
    have hnat' : ev (Work.MotAS.kleinRAS (MvPolynomial.C a) (MvPolynomial.C b)
          (MvPolynomial.C g)
          ![1, MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, 0] j)
        = Work.MotAS.kleinRAS (ev (MvPolynomial.C a)) (ev (MvPolynomial.C b))
            (ev (MvPolynomial.C g))
            (fun j => ev (![1, MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, 0] j)) j :=
      hnat.symm
    rw [hnat', hca, hcb, hcg, hwv]
    simpa using congrFun (Work.MotAS.kleinRAS_chart_eq_zero a' b' g'
      (c 0) (c 1) (c 2) (c 3) hc0 hklein') j
  have hZI : Ideal.radical (Work.MotAS.ZIAS a b g) ≤ RingHom.ker ev := by
    refine (RingHom.ker_isPrime ev).radical_le_iff.mpr ?_
    rw [Work.MotAS.ZIAS, Ideal.span_le]
    rintro p ⟨j, rfl⟩
    exact RingHom.mem_ker.mpr (hbZ j)
  let ψ : ASrulA a b g →ₐ[K] k' :=
    Ideal.Quotient.liftₐ (Ideal.radical (Work.MotAS.ZIAS a b g)) ev
      (fun p hp => RingHom.mem_ker.mp (hZI hp))
  have hψ : ∀ p : MvPolynomial (Fin 3) K,
      ψ (Ideal.Quotient.mk (Ideal.radical (Work.MotAS.ZIAS a b g)) p) = ev p := by
    intro p
    show (Ideal.Quotient.lift (Ideal.radical (Work.MotAS.ZIAS a b g))
        (ev : MvPolynomial (Fin 3) K →+* k')
        (fun p hp => RingHom.mem_ker.mp (hZI hp)))
        (Ideal.Quotient.mk (Ideal.radical (Work.MotAS.ZIAS a b g)) p) = ev p
    rw [Ideal.Quotient.lift_mk]
    rfl
  -- ## 9.  The localised evaluation `σ : A[T][1/ε] → k'`
  let σ₀ : Polynomial (ASrulA a b g) →ₐ[K] k' :=
    Polynomial.eval₂AlgHom ψ ((a' + 2 * b') * (y 3 / y 4))
      (fun c => Commute.all (ψ c) ((a' + 2 * b') * (y 3 / y 4)))
  have hσ₀C : ∀ p : ASrulA a b g, σ₀ (Polynomial.C p) = ψ p := by
    intro p
    change Polynomial.eval₂ (ψ : ASrulA a b g →+* k') ((a' + 2 * b') * (y 3 / y 4))
      (Polynomial.C p) = ψ p
    rw [Polynomial.eval₂_C]
    rfl
  have hσ₀X : σ₀ Polynomial.X = (a' + 2 * b') * (y 3 / y 4) := by
    change Polynomial.eval₂ (ψ : ASrulA a b g →+* k') ((a' + 2 * b') * (y 3 / y 4))
      Polynomial.X = (a' + 2 * b') * (y 3 / y 4)
    rw [Polynomial.eval₂_X]
  have hσ₀ε : σ₀ (Polynomial.C (ASrulEpsA a b g)) = ev (Work.MotAS.ASRul.kbRw a b g 4) := by
    rw [hσ₀C]
    exact hψ (Work.MotAS.ASRul.kbRw a b g 4)
  have hεunit : IsUnit (σ₀ (Polynomial.C (ASrulEpsA a b g))) := by
    rw [hσ₀ε]
    exact isUnit_iff_ne_zero.mpr hevW4ne
  let σ : Localization.Away (Polynomial.C (ASrulEpsA a b g)) →ₐ[K] k' :=
    IsLocalization.Away.liftAlgHom (R := Polynomial (ASrulA a b g))
      (S := Localization.Away (Polynomial.C (ASrulEpsA a b g)))
      (x := Polynomial.C (ASrulEpsA a b g)) (f := σ₀) hεunit
  have hσam : ∀ p : Polynomial (ASrulA a b g),
      σ (algebraMap (Polynomial (ASrulA a b g))
          (Localization.Away (Polynomial.C (ASrulEpsA a b g))) p) = σ₀ p := by
    intro p
    change IsLocalization.Away.lift (Polynomial.C (ASrulEpsA a b g)) hεunit
      (algebraMap (Polynomial (ASrulA a b g))
        (Localization.Away (Polynomial.C (ASrulEpsA a b g))) p) = σ₀ p
    exact IsLocalization.Away.lift_eq (Polynomial.C (ASrulEpsA a b g)) hεunit p
  -- ## 10.  `σ ∘ θ = f`
  have hX : ∀ j : Fin 3,
      σ (ASrulTheta a b g hDZ (MvPolynomial.X j)) = f (MvPolynomial.X j) := by
    intro j
    let zvj : Polynomial (ASrulA a b g) :=
      Polynomial.C (Ideal.Quotient.mk (Ideal.radical (Work.MotAS.ZIAS a b g))
          (Work.MotAS.ASRul.kbRv a b g (Work.MotAS.asCh3 j))) * Polynomial.X
        + Polynomial.C (Ideal.Quotient.mk (Ideal.radical (Work.MotAS.ZIAS a b g))
          (Work.MotAS.ASRul.kbRw a b g (Work.MotAS.asCh3 j)))
    have hθX : ASrulTheta a b g hDZ (MvPolynomial.X j)
        = IsLocalization.mk' (Localization.Away (Polynomial.C (ASrulEpsA a b g))) zvj
            ⟨Polynomial.C (ASrulEpsA a b g), Submonoid.mem_powers _⟩ := by
      rw [ASrulTheta]
      exact MvPolynomial.aeval_X _ _
    have hspec := IsLocalization.mk'_spec
      (S := Localization.Away (Polynomial.C (ASrulEpsA a b g)))
      (M := Submonoid.powers (Polynomial.C (ASrulEpsA a b g))) zvj
      ⟨Polynomial.C (ASrulEpsA a b g), Submonoid.mem_powers _⟩
    have hzv : σ₀ zvj = ev (Work.MotAS.ASRul.kbRv a b g (Work.MotAS.asCh3 j))
          * ((a' + 2 * b') * (y 3 / y 4))
        + ev (Work.MotAS.ASRul.kbRw a b g (Work.MotAS.asCh3 j)) := by
      change σ₀ (Polynomial.C (Ideal.Quotient.mk (Ideal.radical (Work.MotAS.ZIAS a b g))
            (Work.MotAS.ASRul.kbRv a b g (Work.MotAS.asCh3 j))) * Polynomial.X
          + Polynomial.C (Ideal.Quotient.mk (Ideal.radical (Work.MotAS.ZIAS a b g))
            (Work.MotAS.ASRul.kbRw a b g (Work.MotAS.asCh3 j))))
        = ev (Work.MotAS.ASRul.kbRv a b g (Work.MotAS.asCh3 j))
            * ((a' + 2 * b') * (y 3 / y 4))
          + ev (Work.MotAS.ASRul.kbRw a b g (Work.MotAS.asCh3 j))
      rw [map_add, map_mul, hσ₀C, hσ₀C, hσ₀X, hψ, hψ]
    have hstep : σ (IsLocalization.mk'
            (Localization.Away (Polynomial.C (ASrulEpsA a b g))) zvj
            ⟨Polynomial.C (ASrulEpsA a b g), Submonoid.mem_powers _⟩)
          * ev (Work.MotAS.ASRul.kbRw a b g 4)
        = ev (Work.MotAS.ASRul.kbRv a b g (Work.MotAS.asCh3 j)) * ((a' + 2 * b') * (y 3 / y 4))
          + ev (Work.MotAS.ASRul.kbRw a b g (Work.MotAS.asCh3 j)) := by
      have h2 := congrArg (fun t => σ t) hspec
      rw [map_mul] at h2
      rw [hσam (Polynomial.C (ASrulEpsA a b g)), hσam zvj, hσ₀ε, hzv] at h2
      exact h2
    have hkey : σ (ASrulTheta a b g hDZ (MvPolynomial.X j))
        = (ev (Work.MotAS.ASRul.kbRv a b g (Work.MotAS.asCh3 j))
              * ((a' + 2 * b') * (y 3 / y 4))
            + ev (Work.MotAS.ASRul.kbRw a b g (Work.MotAS.asCh3 j)))
          / ev (Work.MotAS.ASRul.kbRw a b g 4) := by
      rw [eq_div_iff hevW4ne, hθX]
      exact hstep
    have hpj := hparam j
    rw [← hevR (Work.MotAS.asCh3 j), ← hevR 3, ← hevW (Work.MotAS.asCh3 j), ← hevW 4] at hpj
    rw [hevW4] at hpj
    have hrhs : (ev (Work.MotAS.ASRul.kbRv a b g (Work.MotAS.asCh3 j))
              * ((a' + 2 * b') * (y 3 / y 4))
            + ev (Work.MotAS.ASRul.kbRw a b g (Work.MotAS.asCh3 j)))
          / ev (Work.MotAS.ASRul.kbRw a b g 4) = y (Work.MotAS.asCh3 j) / y 4 := by
      rw [hevW4, hpj]
      field_simp
      try ring
    have hfy : f (MvPolynomial.X j) = y (Work.MotAS.asCh3 j) / y 4 := by
      rw [hchart j, eq_div_iff hy4, mul_comm]
    rw [hkey, hrhs, ← hfy]
  have halg : (σ.toRingHom).comp (ASrulTheta a b g hDZ).toRingHom = loc := by
    refine MvPolynomial.ringHom_ext ?_ ?_
    · intro c
      have h1 : ASrulTheta a b g hDZ (MvPolynomial.C c)
          = algebraMap K (Localization.Away (Polynomial.C (ASrulEpsA a b g))) c :=
        (ASrulTheta a b g hDZ).commutes c
      show σ (ASrulTheta a b g hDZ (MvPolynomial.C c)) = loc (MvPolynomial.C c)
      rw [h1, σ.commutes c]
      exact (hfC c).symm
    · intro j
      show σ (ASrulTheta a b g hDZ (MvPolynomial.X j)) = loc (MvPolynomial.X j)
      rw [hX j]
  -- ## 11.  Conclusion
  intro p hp
  have hθ0 : ASrulTheta a b g hDZ p = 0 := RingHom.mem_ker.mp hp
  have hσp : σ (ASrulTheta a b g hDZ p) = f p := by
    have h := congrArg (fun (φ : MvPolynomial (Fin 3) K →+* k') => φ p) halg
    rw [RingHom.comp_apply] at h
    exact h
  rw [hθ0, map_zero] at hσp
  exact (hfk p).mp hσp.symm

/-- **The kernel of the AS ruling presentation is contained in every height-one prime at which the
source ruling quintic `sAS2` vanishes and at which `fwVecAS2 · 0` and `fwVecAS2 · 3` do not.** -/
theorem ASrulTheta_ker_le (K : Type) [Field K] [CharP K 5] (a b g : K)
    (hDZ : IsDomain (Work.MotC5N3.ASrulA a b g)) (hε : Work.MotC5N3.ASrulEpsA a b g ≠ 0)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hab : a * b ≠ 0) (hg : ¬ ∃ c : K, c ^ 5 - c = g)
    (x : Work.MotA.polySpec K 3) (hcoh : Order.coheight x = 1)
    (hx : Work.MotAS.sAS2 a b g ∈ x.asIdeal)
    (hfw : Work.MotAS.fwVecAS2 a b g 0 ∉ x.asIdeal)
    (h3 : Work.MotAS.fwVecAS2 a b g 3 ∉ x.asIdeal) :
    RingHom.ker (Work.MotC5N3.ASrulTheta a b g hDZ) ≤ x.asIdeal := by
  haveI hxp : x.asIdeal.IsPrime := x.isPrime
  haveI : IsDomain (MvPolynomial (Fin 3) K ⧸ x.asIdeal) := Ideal.Quotient.isDomain _
  have hinj : Function.Injective (algebraMap K (Work.MotV.resF K x)) := by
    intro u v huv
    have h1 : algebraMap K (Work.MotV.resF K x) (u - v) = 0 := by rw [map_sub, huv, sub_self]
    rcases eq_or_ne (u - v) 0 with h0 | hne
    · exact sub_eq_zero.mp h0
    · exfalso
      have h2 : algebraMap K (Work.MotV.resF K x) (u - v)
          * algebraMap K (Work.MotV.resF K x) ((u - v)⁻¹) = 1 := by
        rw [← map_mul, mul_inv_cancel₀ hne, map_one]
      rw [h1, zero_mul] at h2
      exact one_ne_zero h2.symm
  exact ASrulTheta_ker_le_aux K a b g hDZ hε ha hab hg x hcoh hx hfw h3
    (Work.MotV.resF K x) hinj

end Work.MotC5N3
