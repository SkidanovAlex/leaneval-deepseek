import Mathlib
import Submission.Work.Horn.germF0_base
import Submission.Work.Horn.basin_basic_Dg
import Submission.Work.Horn.flower_q_component_nz

namespace Work.Horn

/-!
# `Work.Horn.flower_petals_Dg` — the Leau–Fatou flower of the pushed-down horn map

For an `𝓕₀`-germ `f₀` with §4.1 data `d` and a nonempty immediate basin `B`, the domain of the
pushed-down horn map is `D_g = {0} ∪ π(B̃ᵘ ∪ B̃ˡ)` (`B̃ᵘ = BuOf d B`, `B̃ˡ = BlOf d B`).  We produce
the Leau–Fatou flower of `g = pushdown d.E` on `D_g`, in the form needed by the `q = 1` step of
§6 (`Work.Horn.q_eq_one`) and by the `V_n`-chain construction (`NOTES_SESSION7.md`):

`q` disjoint open connected petals `V i ⊆ D_g`, none of them containing `0`, all accumulating at
`0`, invariant up to the fixed point (`g (V i) ⊆ V i ∪ {0}`), with `g` injective on each `V i`,
whose union captures the whole parabolic basin of `g` on `D_g`, and which form a Markov partition
of the basin (the "which petal is entered" index is locally constant on the basin).

The mathematics is entirely the local flower theorem for the germ
`g ζ = ζ + a ζ^(q+1) + o(ζ^(q+1))` (`hgerm`, with `a ≠ 0`): the local *germ* is `hgerm`, the
openness hypothesis `hopen` (holomorphic + nowhere locally constant) is supplied by the caller, and
the *connectedness* of `D_g` is **not** needed and is in fact false
(`Work.Horn.not_preconnected_Dg`), so we use the component version
`Work.Horn.flower_q_component_nz` (Leau–Fatou flower on an open `D ∋ 0` with `hopen`, with no
petal meeting `0`).  The three inputs it still needs are all structural facts about `g` on `D_g`
proved elsewhere in the workspace:

* `IsOpen D_g` — `isOpen_insert_piExp`, from Prop. 5.3's topology of `B̃ᵘ`, `B̃ᵈ`
  (`Work.HornTopo.horn_topo`: they are open and contain the half planes `{±Im > η₀}`);
* `DifferentiableOn ℂ (pushdown d.E) D_g` — `pushdown_g_holo`;
* `pushdown d.E 0 = 0` — the definition of `pushdown`.
-/

open MandelDim Set Filter Topology
open scoped Topology

theorem flower_petals_Dg {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hBne : B.Nonempty)
    (hopen : ∀ z ∈ insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B)),
      ∀ U ∈ nhds z, MandelDim.pushdown d.E '' U ∈ nhds (MandelDim.pushdown d.E z))
    {q : ℕ} {a : ℂ} (hq : 1 ≤ q) (ha : a ≠ 0)
    (hgerm : Filter.Tendsto (fun ζ : ℂ =>
        (MandelDim.pushdown d.E ζ - ζ - a * ζ ^ (q + 1)) / ζ ^ (q + 1))
      (nhdsWithin 0 {0}ᶜ) (nhds 0)) :
    ∃ V : Fin q → Set ℂ,
      (∀ i, IsOpen (V i) ∧ IsConnected (V i) ∧
        V i ⊆ insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B))) ∧
      (∀ i, (0 : ℂ) ∉ V i) ∧
      (∀ i, ∀ z ∈ V i, MandelDim.pushdown d.E z ∈ V i ∪ {0}) ∧
      (∀ i j : Fin q, i ≠ j → Disjoint (V i) (V j)) ∧
      (∀ i, (0 : ℂ) ∈ closure (V i)) ∧
      (∀ i, Set.InjOn (MandelDim.pushdown d.E) (V i)) ∧
      (∀ z ∈ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
          (insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B))),
        ∃ n : ℕ, (MandelDim.pushdown d.E)^[n] z ∈ ⋃ i, V i) ∧
      (∀ z ∈ insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B)),
        (∃ n : ℕ, (∀ k < n, (MandelDim.pushdown d.E)^[k] z ∈
            insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B))) ∧
          (MandelDim.pushdown d.E)^[n] z ∈ ⋃ i, V i) →
        z ∈ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
          (insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B)))) ∧
      (∀ z ∈ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
          (insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B))),
        ∃ U ∈ nhds z, ∀ w ∈ U, ∀ i : Fin q,
          ((∃ n : ℕ, (MandelDim.pushdown d.E)^[n] z ∈ V i) ↔
            (∃ n : ℕ, (MandelDim.pushdown d.E)^[n] w ∈ V i))) := by
  -- the immediate basin carries the `𝓕₀`-setup, so Prop. 5.3 applies to `BuOf d B`, `BlOf d B`
  obtain ⟨c, hsetup⟩ := isF0Setup_of_immediateBasin hF0 d hB hBne
  obtain ⟨hBuO, hBlO, hBuT, hBlT, hup, hlo, hsub⟩ :=
    Work.HornTopo.horn_topo f₀ D₀ B c d hsetup
  -- the three structural facts about `g = pushdown d.E` on `D_g`
  have hDg_open : IsOpen
      (insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B))) :=
    isOpen_insert_piExp hBuO hBlO hup hlo
  have hDg_holo : DifferentiableOn ℂ (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B))) :=
    pushdown_g_holo hF0 d hB hBne (BuOf_eq_component d B) (BlOf_eq_component d B)
      hsub hup hlo
  have hDg_zero : MandelDim.pushdown d.E 0 = 0 := MandelDim.pushdown_zero d.E
  -- the local flower theorem for the parabolic germ `ζ ↦ ζ + a ζ^(q+1) + o(ζ^(q+1))`
  exact flower_q_component_nz (f := MandelDim.pushdown d.E)
    (D := insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B)))
    hDg_open (Set.mem_insert 0 _) hDg_holo hq ha hDg_zero hopen hgerm

end Work.Horn
