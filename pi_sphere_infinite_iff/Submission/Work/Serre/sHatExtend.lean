import Mathlib
import Submission.Work.Serre.E2bDefs
import Submission.Work.Serre.HatExtend
import Submission.Work.RatHurewicz.Bridge.exists_collapse_simplex
import Submission.Work.Serre.E0SimplexBdryExt

/-!
# The hat extension lemma for the standard simplex

`Work.Serre.sHatExtend`: a continuous map on the hat `sHat n = (Δⁿ × {0}) ∪ (∂Δⁿ × I)` whose outer
boundary `sHatBdry n = ∂Δⁿ × {1}` lands in `A` extends to `Δⁿ × I` with the top face `Δⁿ × {1}`
landing in `A`, provided the compression property `CompressRel X A n` holds.

The proof transports the cube version `Work.Serre.hatExtend` along the collapse
`Φ = H n × id : Iⁿ × I → Δⁿ × I`.  The map `Φ` is a quotient map (a closed surjection of compact
spaces) whose non-trivial fibres are contained in `∂Iⁿ × I`, where the extension is a pullback of a
map on `sHat n` and hence constant on fibres; so the cube extension descends.
-/

open scoped Topology unitInterval
open Work.Stems.Cubical

namespace Work.Serre

noncomputable section

open Work.RatHurewicz.Bridge
open Work.RatHurewicz (H H_apply Hfun)

/-- The collapse of the cube onto the standard simplex, times the identity. -/
def collapseProj (n : ℕ) :
    C(IC n × unitInterval, ↥(stdSimplex ℝ (Fin (n + 1))) × unitInterval) where
  toFun p := ((H n) p.1, p.2)
  continuous_toFun :=
    Continuous.prodMk ((H n).continuous.comp continuous_fst) continuous_snd

@[simp]
theorem collapseProj_apply (n : ℕ) (p : IC n × unitInterval) :
    collapseProj n p = ((H n) p.1, p.2) := rfl

theorem continuous_collapseProj (n : ℕ) : Continuous (collapseProj n) :=
  (collapseProj n).continuous

/-- A chosen preimage of a point of the simplex under the collapse `H n`. -/
def simplexPreimage (n : ℕ) (z : ↥(stdSimplex ℝ (Fin (n + 1)))) : IC n :=
  Classical.choose (H_surjective n z)

theorem collapse_simplexPreimage (n : ℕ) (z : ↥(stdSimplex ℝ (Fin (n + 1)))) :
    (H n) (simplexPreimage n z) = z :=
  Classical.choose_spec (H_surjective n z)

/-- The collapse of the cube maps the cube hat into the simplex hat. -/
theorem mem_sHat_of_LSet {n : ℕ} (y : IC n) (t : unitInterval)
    (h : (y, t) ∈ Work.StemsB.LSet n) : ((H n) y, t) ∈ sHat n := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (H_mem_simplexBdry n y h)

theorem sHatExtend {X : Type} [TopologicalSpace X] {A : Set X} {n : ℕ} (hn : 1 ≤ n)
    (hc : Work.RatHurewicz.CompressRel X A n)
    (f : C(↥(sHat n), X))
    (hf : ∀ q : ↥(sHat n),
      (q : ↥(stdSimplex ℝ (Fin (n + 1))) × unitInterval) ∈ sHatBdry n → f q ∈ A) :
    ∃ F : C(↥(stdSimplex ℝ (Fin (n + 1))) × unitInterval, X),
      (∀ q : ↥(sHat n), F q = f q) ∧
      (∀ z : ↥(stdSimplex ℝ (Fin (n + 1))), F (z, 1) ∈ A) := by
  -- the quotient map and its surjectivity
  have hsurj : Function.Surjective (collapseProj n) := by
    intro p
    obtain ⟨z, t⟩ := p
    exact ⟨(simplexPreimage n z, t), by
      simp only [collapseProj_apply, collapse_simplexPreimage n z]⟩
  have hquot : Topology.IsQuotientMap (collapseProj n) :=
    (Continuous.isClosedMap (continuous_collapseProj n)).isQuotientMap
      (continuous_collapseProj n) hsurj
  -- the pullback of `f` to the cube hat
  have hmaps : ∀ p : ↥(Work.StemsB.LSet n),
      collapseProj n (p : IC n × unitInterval) ∈ sHat n :=
    fun p => mem_sHat_of_LSet p.1.1 p.1.2 p.2
  have hmaps_cont : Continuous (fun p : ↥(Work.StemsB.LSet n) =>
      (⟨collapseProj n (p : IC n × unitInterval), hmaps p⟩ : ↥(sHat n))) :=
    Continuous.subtype_mk ((continuous_collapseProj n).comp
      (continuous_subtype_val : Continuous
        (fun p : ↥(Work.StemsB.LSet n) => (p : IC n × unitInterval)))) _
  let f' : C(↥(Work.StemsB.LSet n), X) :=
    f.comp ⟨fun p => ⟨collapseProj n (p : IC n × unitInterval), hmaps p⟩, hmaps_cont⟩
  have hf'_apply : ∀ p : ↥(Work.StemsB.LSet n),
      f' p = f ⟨collapseProj n (p : IC n × unitInterval), hmaps p⟩ := fun p => rfl
  have hf' : ∀ q : ↥(Work.StemsB.LSet n),
      (q : IC n × unitInterval) ∈ hatBdry n → f' q ∈ A := by
    intro q hq
    obtain ⟨h1, h2⟩ := hq
    rw [hf'_apply]
    refine hf _ ⟨H_mem_simplexBdry n q.1.1 h1, h2⟩
  -- the cube extension
  obtain ⟨G, hGhat, hGtop⟩ := hatExtend hn hc f' hf'
  have hG_LSet : ∀ (y : IC n) (t : unitInterval) (hy : (y, t) ∈ Work.StemsB.LSet n),
      G (y, t) = f ⟨((H n) y, t), mem_sHat_of_LSet y t hy⟩ := by
    intro y t hy
    rw [hGhat ⟨(y, t), hy⟩, hf'_apply]
    rfl
  -- the descended map
  let Ffun : ↥(stdSimplex ℝ (Fin (n + 1))) × unitInterval → X :=
    fun p => G (simplexPreimage n p.1, p.2)
  have hHx : ∀ z : ↥(stdSimplex ℝ (Fin (n + 1))), (H n) (simplexPreimage n z) = z :=
    collapse_simplexPreimage n
  -- `Ffun ∘ Φ = G`
  have hFcomp : ∀ p : IC n × unitInterval, Ffun (collapseProj n p) = G p := by
    intro p
    obtain ⟨x, t⟩ := p
    show G (simplexPreimage n ((H n) x), t) = G (x, t)
    rcases H_eq_or_boundary n (hHx ((H n) x)) with heq | ⟨hb, hb'⟩
    · exact congrArg (fun w => G (w, t)) heq
    · rw [hG_LSet (simplexPreimage n ((H n) x)) t (Or.inr hb),
        hG_LSet x t (Or.inr hb')]
      refine congrArg f (Subtype.ext ?_)
      simp only [collapseProj_apply, hHx ((H n) x)]
  have hFcomp' : (Ffun ∘ collapseProj n) = ⇑G := funext hFcomp
  have hFcont : Continuous Ffun := hquot.continuous_iff.mpr (hFcomp' ▸ G.continuous)
  -- the values on the hat
  have hFhat : ∀ q : ↥(sHat n), Ffun q = f q := by
    intro q
    obtain ⟨⟨z, t⟩, hq⟩ := q
    show G (simplexPreimage n z, t) = f ⟨(z, t), hq⟩
    by_cases ht : t = 0
    · rw [hG_LSet (simplexPreimage n z) t (Or.inl ht)]
      refine congrArg f (Subtype.ext ?_)
      simp only [hHx z]
    · have hb : z ∈ simplexBdry n := by
        rcases hq with h | h
        · exact absurd h ht
        · exact h
      obtain ⟨i, hi⟩ := hb
      have hcube : simplexPreimage n z ∈ Cube.boundary (Fin n) :=
        Hfun_zero_mem_boundary (simplexPreimage n z)
          ⟨i, by rw [← H_apply, hHx z]; exact hi⟩
      rw [hG_LSet (simplexPreimage n z) t (Or.inr hcube)]
      refine congrArg f (Subtype.ext ?_)
      simp only [hHx z]
  exact ⟨⟨Ffun, hFcont⟩, hFhat, fun z => hGtop (simplexPreimage n z)⟩

end

end Work.Serre
