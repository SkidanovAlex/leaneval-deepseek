import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Interfaces.HornParts
import Submission.Work.Horn.germF0_base
import Submission.Work.Horn.image_eq_of_compact_preimage
import Submission.Work.Horn.hopen_Dg
import Submission.Work.Horn.E_not_locally_const
import Submission.Work.Horn.petal_components_upper_local
import Submission.Work.Horn.spread_chain_nesting

/-!
# `Work.Horn.chain_onto_of_proper`

The spread chain `W` of Shishikura's Lemma 5.4 is built as a chain of *preimages*: level `n + 1`
is a union of connected components of `D_g ∩ g⁻¹(W n i)` meeting `W n i`, so that by construction
`g` maps `W (n + 1) i` into `W n i ∪ {0}`.  For the counting argument (Lemma 5.2: one critical
point forbids two disjoint immediate basins) one needs the *reverse* inclusion as well, i.e. that
`g` maps `W (n + 1) i` **onto** `W n i`.  This is the statement proved here: the covering/properness
hypothesis `hprop` — preimages of compact subsets of `W n i` are compact inside `W (n + 1) i` —
upgrades the inclusion to an equality.

The mathematical content is Shishikura's: a proper holomorphic map onto a connected open set is
surjective, because its image is both open (open mapping theorem) and relatively closed (properness
+ completeness of the plane), and nonempty (it contains the image of any point of `W (n+1) i`).
This is packaged in `Work.Horn.image_eq_of_compact_preimage`.

Two inputs about the ambient horn map `g = pushdown Ẽ` are needed and are supplied by the
`Work.Horn` library (all sorry-free, from `Work.Horn.germF0_base`):

* `D_g = {0} ∪ π(Bu ∪ Bl)` is **open** (`Work.Horn.isOpen_insert_piExp`), from the openness of the
  `T`-invariant upper/lower components `Bu`, `Bl` of `φ₀⁻¹(B) ∩ Dφ` (Prop. 5.3,
  `Work.Horn.horn_topo_facts`);
* `g` is **holomorphic** on `D_g` (`Work.Horn.pushdown_g_holo`).

Also used: for `ζ ≠ 0` the pushed-down horn map never vanishes — `pushdown E ζ = π(E (log ζ /2πi))`
and `π = exp` has no zero — so the spurious `{0}` in the inclusion `g '' W (n+1) i ⊆ W n i ∪ {0}`
is impossible, since `0 ∉ W (n+1) i`.
-/

namespace Work.Horn

/-- The pushed-down horn map is nowhere zero away from `0`: `pushdown E ζ = π(E (log ζ /(2πi)))`
and `π = exp` takes no value `0`. -/
theorem pushdown_ne_zero_of_ne_zero (E : ℂ → ℂ) {ζ : ℂ} (hζ : ζ ≠ 0) :
    MandelDim.pushdown E ζ ≠ 0 := by
  rw [MandelDim.pushdown]
  simp only [MandelDim.piExp, hζ, ite_false]
  exact Complex.exp_ne_zero _

theorem chain_onto_of_proper {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hBne : B.Nonempty) {η : ℝ} {Bu Bl : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl)
    {q : ℕ} {V : Fin q → Set ℂ} {W : ℕ → Fin q → Set ℂ}
    (hWopen : ∀ (n : ℕ) (i : Fin q), IsOpen (W n i))
    (hWconn : ∀ (n : ℕ) (i : Fin q), IsConnected (W n i))
    (hWsub : ∀ (n : ℕ) (i : Fin q), W n i ⊆ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))
    (hWne : ∀ (n : ℕ) (i : Fin q), (0 : ℂ) ∉ W n i)
    (hWmap : ∀ (n : ℕ) (i : Fin q),
      Set.MapsTo (MandelDim.pushdown d.E) (W (n + 1) i) (W n i ∪ {0}))
    (hprop : ∀ (n : ℕ) (i : Fin q) (L : Set ℂ), L ⊆ W n i → IsCompact L →
      IsCompact (W (n + 1) i ∩ (MandelDim.pushdown d.E) ⁻¹' L)) :
    ∀ (n : ℕ) (i : Fin q), MandelDim.pushdown d.E '' W (n + 1) i = W n i := by
  -- the horn domain `D_g = {0} ∪ π(Bu ∪ Bl)` is open and the horn map is holomorphic on it
  obtain ⟨hBuO, hBlO, -, -, -, -, -⟩ := horn_topo_facts hF0 d hB hBne hBu hBl hup hlo
  have hDgOpen : IsOpen (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) :=
    isOpen_insert_piExp hBuO hBlO hup hlo
  have hDgDiff : DifferentiableOn ℂ (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) :=
    pushdown_g_holo hF0 d hB hBne hBu hBl hsub hup hlo
  intro n i
  -- a proper holomorphic map onto a connected open set is onto
  refine image_eq_of_compact_preimage hDgOpen hDgDiff (hWopen n i) (hWsub n i) (hWconn n i)
    (hWopen (n + 1) i) (hWsub (n + 1) i) (hWconn (n + 1) i).nonempty ?_ ?_
  · -- `g '' W (n+1) i ⊆ W n i`: the inclusion modulo `{0}` of `hWmap`, and `g` never takes the
    -- value `0` off `0`, which does not lie in `W (n+1) i`
    rintro z ⟨y, hy, rfl⟩
    have hy0 : y ≠ 0 := fun h => hWne (n + 1) i (h ▸ hy)
    rcases hWmap n i hy with h | h
    · exact h
    · exact absurd (Set.mem_singleton_iff.mp h) (pushdown_ne_zero_of_ne_zero d.E hy0)
  · intro L hL hLc
    exact hprop n i L hL hLc

end Work.Horn
