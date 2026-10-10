import Mathlib
import Submission.Work.MotK.TwRuling.KleinKerDefs
import Submission.Work.MotK.TwRuling.Q_eq_span_sdTFn
import Submission.Work.MotK.TwRuling.sdTFn_linearIndependent

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The kernel of the Klein evaluation: assembly

Main content: for `D : KleinData K` with `D.Good`, a field extension `L/K` and a homogeneous
polynomial `F` of degree `n` with `F(κ₀,…,κ₄) = 0` (where `κᵢ = kleinCoord D L i`), the polynomial
`F` lies in the Pfaffian ideal `(p₀,…,p₄)`.

The argument is a dimension count in each degree `n`:

* `kleinKerSub L a b` (the Pfaffian ideal) lies in the kernel of the evaluation
  (`hD.klein_eq`), and the degree-`n` part of `L[X₀,…,X₄]` is contained in
  `kleinKerSub L a b ⊔ span (range (stdMono L n))` (the normal-form reduction
  `hom_le_kleinKer_sup_std`);
* `span (range (stdMono L n))` has dimension `≤ 5n`, while `Five.Q (D.E.baseChange L) n` (the span
  of the `n`-fold products of `L(5·O) = span{1,x,y,x²,xy}`) has dimension `≥ 5n`
  (`finrank_Q`) and is contained in the image of the degree-`n` homogeneous polynomials
  (`Q_le_aeval_homogeneousSubmodule`);
* hence the restriction of the evaluation to `span (range (stdMono L n))` is injective, and
  `F = G + H` with `G` in that span and `H` in the ideal forces `G = 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotK.TwRuling

noncomputable section

/-! ## §1 The evaluation kills the Pfaffian ideal -/

theorem aeval_kleinP_eq_zero (K : Type) [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (L : Type) [Field L] [Algebra K L] (k : Fin 5) :
    MvPolynomial.aeval (Work.MotV.kleinCoord D L)
        (Work.MotK.kleinP (MvPolynomial.C (algebraMap K L D.a))
          (MvPolynomial.C (algebraMap K L D.b)) (fun i => MvPolynomial.X i) k) = 0 := by
  have hkey : MvPolynomial.aeval (Work.MotV.kleinCoord D L)
        (Work.MotK.kleinP (MvPolynomial.C (algebraMap K L D.a))
          (MvPolynomial.C (algebraMap K L D.b)) (fun i => MvPolynomial.X i) k)
      = Work.MotK.kleinP (algebraMap L (Affine.FunctionField (D.E.baseChange L))
            (algebraMap K L D.a))
          (algebraMap L (Affine.FunctionField (D.E.baseChange L)) (algebraMap K L D.b))
          (Work.MotV.kleinCoord D L) k := by
    fin_cases k <;>
      simp only [Work.MotK.kleinP_zero', Work.MotK.kleinP_one', Work.MotK.kleinP_two',
        Work.MotK.kleinP_three', Work.MotK.kleinP_four', Work.MotK.kleinP0, Work.MotK.kleinP1,
        Work.MotK.kleinP2, Work.MotK.kleinP3, Work.MotK.kleinP4, map_add, map_sub, map_mul,
        map_pow, map_neg, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  rw [hkey]
  have h1 : (algebraMap L (Affine.FunctionField (D.E.baseChange L)) (algebraMap K L D.a))
      = algebraMap K (Affine.FunctionField (D.E.baseChange L)) D.a :=
    (IsScalarTower.algebraMap_apply K L _ D.a).symm
  have h2 : (algebraMap L (Affine.FunctionField (D.E.baseChange L)) (algebraMap K L D.b))
      = algebraMap K (Affine.FunctionField (D.E.baseChange L)) D.b :=
    (IsScalarTower.algebraMap_apply K L _ D.b).symm
  rw [h1, h2]
  exact hD.klein_eq L k

theorem aeval_mem_kleinKerSub (K : Type) [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (L : Type) [Field L] [Algebra K L] (x : MvPolynomial (Fin 5) L)
    (hx : x ∈ kleinKerSub L (algebraMap K L D.a) (algebraMap K L D.b)) :
    MvPolynomial.aeval (Work.MotV.kleinCoord D L) x = 0 := by
  have hx' : x ∈ Ideal.span (Set.range (fun k : Fin 5 =>
      Work.MotK.kleinP (MvPolynomial.C (algebraMap K L D.a))
        (MvPolynomial.C (algebraMap K L D.b)) (fun i => MvPolynomial.X i) k)) := hx
  refine Submodule.span_induction (p := fun x _ =>
      MvPolynomial.aeval (Work.MotV.kleinCoord D L) x = 0) ?_ ?_ ?_ ?_ hx'
  · rintro y ⟨k, rfl⟩
    exact aeval_kleinP_eq_zero K D hD L k
  · simp
  · intro y z hy hz hpy hpz
    rw [map_add, hpy, hpz, add_zero]
  · intro c y hy hpy
    rw [smul_eq_mul, map_mul, hpy, mul_zero]

/-! ## §2 The `n = 0` cases -/

theorem Q_zero (R : Type) [Field R] (E : WeierstrassCurve R) :
    Work.MotK.TwRuling.Five.Q E 0 = Submodule.span R {(1 : Affine.FunctionField E)} := by
  have hset : Set.range (fun q : Fin 0 → Fin 5 => ∏ i : Fin 0, sdBas E (q i))
      = {(1 : Affine.FunctionField E)} := by
    ext z
    constructor
    · rintro ⟨q, rfl⟩
      simp
    · rintro rfl
      exact ⟨Fin.elim0, by simp⟩
  unfold Work.MotK.TwRuling.Five.Q
  rw [hset]



/-! ## §3 The dimension bounds -/

/-- The `n`-fold products of the basis `1, x, y, x², xy` span a space of dimension `5n`, for
`n ≥ 1`. -/
theorem finrank_Q (R : Type) [Field R] (E : WeierstrassCurve R) (n : ℕ) (hn : 1 ≤ n) :
    Module.finrank R (Work.MotK.TwRuling.Five.Q E n) = 5 * n := by
  rw [Q_eq_span_sdTFn R E n, finrank_span_eq_card (sdTFn_linearIndependent R E n),
    card_sdTFn_index n hn]

/-- The dimension of the span of the standard monomials of degree `n` is at most the dimension of
`Five.Q E n` (which is `5n` for `n ≥ 1`, and `1` for `n = 0`). -/
theorem finrank_stdSpan_le (K : Type) [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (L : Type) [Field L] [Algebra K L] (n : ℕ) :
    Module.finrank L (Submodule.span L (Set.range (stdMono L n))) ≤
      Module.finrank L (Work.MotK.TwRuling.Five.Q (D.E.baseChange L) n) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    haveI : Fintype ↥(Set.range (stdMono L 0)) := (Set.finite_range _).fintype
    have hcard0 : Fintype.card (stdIdx 0) = 1 := by
      have h : Fintype.card (stdIdx 0) = ∑ j : Fin 5, Fintype.card (Fin (0 + 1 - tt j)) :=
        Fintype.card_sigma
      rw [h]
      simp only [Fintype.card_fin]
      rw [Fin.sum_univ_five]
      have h0 : tt (0 : Fin 5) = 0 := by decide
      have h1 : tt (1 : Fin 5) = 1 := by decide
      have h2 : tt (2 : Fin 5) = 1 := by decide
      have h3 : tt (3 : Fin 5) = 1 := by decide
      have h4 : tt (4 : Fin 5) = 2 := by decide
      rw [h0, h1, h2, h3, h4]
    have hQ0 : Module.finrank L (Work.MotK.TwRuling.Five.Q (D.E.baseChange L) 0) = 1 := by
      rw [Q_zero,
        finrank_span_singleton
          (show (1 : Affine.FunctionField (D.E.baseChange L)) ≠ 0 by simp)]
    calc Module.finrank L (Submodule.span L (Set.range (stdMono L 0)))
        ≤ (Set.range (stdMono L 0)).toFinset.card := finrank_span_le_card _
      _ = Fintype.card ↥(Set.range (stdMono L 0)) := Set.toFinset_card _
      _ ≤ Fintype.card (stdIdx 0) := Fintype.card_range_le _
      _ = 1 := hcard0
      _ = Module.finrank L (Work.MotK.TwRuling.Five.Q (D.E.baseChange L) 0) := hQ0.symm
  · haveI : Fintype ↥(Set.range (stdMono L n)) := (Set.finite_range _).fintype
    have hcard : Fintype.card (stdIdx n) = 5 * n := card_stdIdx n hn
    have hQ : Module.finrank L (Work.MotK.TwRuling.Five.Q (D.E.baseChange L) n) = 5 * n :=
      finrank_Q L (D.E.baseChange L) n hn
    calc Module.finrank L (Submodule.span L (Set.range (stdMono L n)))
        ≤ (Set.range (stdMono L n)).toFinset.card := finrank_span_le_card _
      _ = Fintype.card ↥(Set.range (stdMono L n)) := Set.toFinset_card _
      _ ≤ Fintype.card (stdIdx n) := Fintype.card_range_le _
      _ = 5 * n := hcard
      _ = Module.finrank L (Work.MotK.TwRuling.Five.Q (D.E.baseChange L) n) := hQ.symm

/-! ## §4 The main statement -/

theorem kleinKer_mem_of_homogeneous_aeval_eq_zero (K : Type) [Field K]
    (D : Work.MotV.KleinData K) (hD : D.Good)
    (L : Type) [Field L] [Algebra K L] (n : ℕ) (F : MvPolynomial (Fin 5) L)
    (hF : F ∈ MvPolynomial.homogeneousSubmodule (Fin 5) L n)
    (hF0 : MvPolynomial.aeval (Work.MotV.kleinCoord D L) F = 0) :
    F ∈ kleinKerIdeal L (algebraMap K L D.a) (algebraMap K L D.b) := by
  have hab : algebraMap K L D.a * algebraMap K L D.b ≠ 0 := by
    rw [← map_mul]
    exact (map_ne_zero_iff _ (algebraMap K L).injective).mpr hD.ab_ne
  set Φ : MvPolynomial (Fin 5) L →ₐ[L] Affine.FunctionField (D.E.baseChange L) :=
    MvPolynomial.aeval (Work.MotV.kleinCoord D L) with hΦdef
  set Il := kleinKerSub L (algebraMap K L D.a) (algebraMap K L D.b) with hIdef
  set S : Submodule L (MvPolynomial (Fin 5) L) :=
    Submodule.span L (Set.range (stdMono L n)) with hSdef
  -- §4.1 `Φ` kills `Il`
  have hmapI : Submodule.map Φ.toLinearMap Il = ⊥ := by
    rw [eq_bot_iff, Submodule.map_le_iff_le_comap]
    intro x hx
    rw [Submodule.mem_comap, Submodule.mem_bot]
    rw [hIdef] at hx
    exact aeval_mem_kleinKerSub K D hD L x hx
  -- §4.2 `Q n ≤ Φ '' S`
  have hQle : Work.MotK.TwRuling.Five.Q (D.E.baseChange L) n ≤
      Submodule.map Φ.toLinearMap (MvPolynomial.homogeneousSubmodule (Fin 5) L n) := by
    -- TODO: replace by `Q_le_aeval_homogeneousSubmodule K D hD L n`
    sorry
  have hred : MvPolynomial.homogeneousSubmodule (Fin 5) L n ≤ Il ⊔ S := by
    -- TODO: replace by `hom_le_kleinKer_sup_std L _ _ hab n`
    sorry
  have hQleS : Work.MotK.TwRuling.Five.Q (D.E.baseChange L) n ≤ Submodule.map Φ.toLinearMap S := by
    refine le_trans hQle ?_
    calc Submodule.map Φ.toLinearMap (MvPolynomial.homogeneousSubmodule (Fin 5) L n)
        ≤ Submodule.map Φ.toLinearMap (Il ⊔ S) := Submodule.map_mono hred
      _ = Submodule.map Φ.toLinearMap Il ⊔ Submodule.map Φ.toLinearMap S :=
          Submodule.map_sup Il S Φ.toLinearMap
      _ = Submodule.map Φ.toLinearMap S := by simp [hmapI]
  -- §4.3 `Φ` is injective on `S`
  haveI hfinS : Module.Finite L ↥S := Module.Finite.span_of_finite L (Set.finite_range _)
  have hker : (Φ.toLinearMap.domRestrict S).ker = ⊥ := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (Φ.toLinearMap.domRestrict S)
    rw [LinearMap.range_domRestrict] at hrn
    have hle1 : Module.finrank L ↥S ≤
        Module.finrank L ↥(Submodule.map Φ.toLinearMap S) :=
      le_trans (finrank_stdSpan_le K D hD L n) (Submodule.finrank_mono hQleS)
    have hle2 : Module.finrank L ↥(Submodule.map Φ.toLinearMap S) ≤ Module.finrank L ↥S :=
      Submodule.finrank_map_le Φ.toLinearMap S
    have hfin : Module.finrank L ↥(Submodule.map Φ.toLinearMap S) = Module.finrank L ↥S :=
      le_antisymm hle2 hle1
    rw [hfin] at hrn
    have h0 : Module.finrank L ↥(Φ.toLinearMap.domRestrict S).ker = 0 := by omega
    exact Submodule.finrank_eq_zero.mp h0
  have hinj : Function.Injective (Φ.toLinearMap.domRestrict S) :=
    LinearMap.ker_eq_bot.mp hker
  -- §4.4 conclude
  have hFsup : F ∈ S ⊔ Il := by
    rw [sup_comm]
    exact hred hF
  obtain ⟨G, hG, H, hH, hGH⟩ := Submodule.mem_sup.mp hFsup
  have hΦH : Φ H = 0 := by
    rw [hIdef] at hH
    exact aeval_mem_kleinKerSub K D hD L H hH
  have hΦG : Φ G = 0 := by
    have h1 : Φ F = Φ G + Φ H := by rw [← hGH, map_add]
    rw [hF0, hΦH, add_zero] at h1
    exact h1.symm
  have hG0 : G = 0 := by
    have h1 : (Φ.toLinearMap.domRestrict S) ⟨G, hG⟩ = 0 := hΦG
    have h2 : (Φ.toLinearMap.domRestrict S) (0 : ↥S) = 0 := map_zero _
    have heq : (⟨G, hG⟩ : ↥S) = 0 := hinj (by rw [h1, h2])
    exact Subtype.ext_iff.mp heq
  have hFH : F = H := by rw [← hGH, hG0, zero_add]
  rw [hFH]
  rw [hIdef] at hH
  exact hH

end

end Work.MotK.TwRuling
