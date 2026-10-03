
import Mathlib
import Submission.Work.Horn.level_bijOn_of_ne_critval
import Submission.Work.Horn.spreadChain_spec
import Submission.Work.Horn.Dg_pieces
import Submission.Work.Horn.basin_basic_Dg
import Submission.Work.Horn.hopen_Dg
import Submission.Work.Horn.zero_not_mem_basin_pushdown
import Submission.Work.Horn.isCompact_inter_preimage_of_chain
import Submission.Work.Horn.spread_chain_nesting
import Submission.Work.BasinSC.cover_basic

/-!
# The structure of the union of Shishikura's spread chain

`Work.Horn.spreadChain_bijOn_structure`: for the pushed-down horn map `g = pushdown d.E` on the
horn domain `D_g = {0} ∪ π '' (Bu ∪ Bl)` and a family `V` of petals, if the critical value
`v = π (Φ c)` is met by no level of the chain `W = spreadChain g D_g V`, then for every index `i`

* `g` maps `W (n+1) i` bijectively onto `W n i` for every `n`,
* the union `B i = ⋃ n, W n i` is simply connected,
* compact subsets of `B i` have compact preimages in `B i` (properness of `g : B i → B i`),
* `B i ⊆ g '' B i`,
* every point of `B i` reaches the petal `V i` in finitely many steps.

The proof is split as follows.

* `spreadChain_union_structure_aux` (pure combinatorics): an increasing chain whose consecutive
  maps are bijections can be "glued": `g` is injective on the union, the union meets every level
  exactly in the next level, it maps onto itself, and every point reaches level `0`.
  (Also available as the standalone module `Submission.Work.Horn.spreadChain_union_structure`.)
* `spreadChain_structure_aux` (abstract reduction): with `g` holomorphic on the open `D`, a covering
  of `D` off `{0, v}` and `v` never met by the chain, each level map is a covering of a simply
  connected base away from the critical value, so it is a bijection
  (`bijOn_and_isCompact_of_isCoveringMapOn`), and each level is simply connected
  (`Work.BasinSC.simplyConnected_of_isCoveringMapOn`).  The union is then simply connected because a
  loop in it is compact and hence lies in a single (open, simply connected) level, and compact
  preimages are computed from the glued preimage identity above.
* The target theorem instantiates the abstract reduction with the horn data: openness/holomorphy of
  `g` on `D_g` (`pushdown_g_holo`), the covering of `D_g` off `{0, v}` (`cov_of_parts` through
  `pushdown_covering`) and the fact that the only critical value of `g` on `D_g` is `v`
  (`pushdown_critval_global_eq`).
-/

set_option linter.ambiguousOpen false
set_option linter.style.haveILetI false

open Set Filter Topology
open scoped Topology

namespace Work.Horn

/-- **Structure of the increasing union of a chain whose consecutive level maps are bijections.**
-/
private theorem spreadChain_union_structure_aux {G : ℂ → ℂ} {q : ℕ} {W : ℕ → Fin q → Set ℂ}
    (i : Fin q) (hmono : ∀ n : ℕ, W n i ⊆ W (n + 1) i)
    (hbij : ∀ n : ℕ, Set.BijOn G (W (n + 1) i) (W n i)) :
    Set.InjOn G (⋃ n, W n i) ∧
      (∀ n : ℕ, (⋃ m, W m i) ∩ G ⁻¹' (W n i) = W (n + 1) i) ∧
      (⋃ n, W n i) ⊆ G '' (⋃ n, W n i) ∧
      (∀ z ∈ ⋃ n, W n i, ∃ n : ℕ, (G^[n]) z ∈ W 0 i) := by
  have hmono_le : ∀ {a b : ℕ}, a ≤ b → W a i ⊆ W b i := by
    intro a b hab
    exact Nat.le_induction subset_rfl (fun n _ ih => Subset.trans ih (hmono n)) b hab
  have hinj_mem : ∀ {a : ℕ} {z z' : ℂ}, z ∈ W a i → z' ∈ W a i → G z = G z' → z = z' := by
    intro a z z' hz hz' h
    cases a with
    | zero => exact (hbij 0).2.1 (hmono 0 hz) (hmono 0 hz') h
    | succ a => exact (hbij a).2.1 hz hz' h
  have hInj : Set.InjOn G (⋃ n, W n i) := by
    intro z hz z' hz' h
    simp only [mem_iUnion] at hz hz'
    obtain ⟨a, ha⟩ := hz
    obtain ⟨b, hb⟩ := hz'
    rcases le_total a b with hab | hba
    · exact hinj_mem (hmono_le hab ha) hb h
    · exact hinj_mem ha (hmono_le hba hb) h
  refine ⟨hInj, ?_, ?_, ?_⟩
  · intro n
    apply Subset.antisymm
    · rintro z ⟨hzU, hzG⟩
      obtain ⟨y, hy, hyg⟩ := (hbij n).2.2 hzG
      have hzy : z = y := hInj hzU (mem_iUnion.mpr ⟨n + 1, hy⟩) (by rw [hyg])
      rwa [hzy]
    · intro z hz
      exact ⟨mem_iUnion.mpr ⟨n + 1, hz⟩, (hbij n).1 hz⟩
  · intro z hz
    simp only [mem_iUnion] at hz
    obtain ⟨k, hk⟩ := hz
    obtain ⟨y, hy, hyg⟩ := (hbij k).2.2 hk
    exact ⟨y, mem_iUnion.mpr ⟨k + 1, hy⟩, hyg⟩
  · have hreachk : ∀ k : ℕ, ∀ z ∈ W k i, (G^[k]) z ∈ W 0 i := by
      intro k
      induction k with
      | zero => intro z hz; simpa using hz
      | succ k ih =>
        intro z hz
        have hGz : G z ∈ W k i := (hbij k).1 hz
        have hh := ih (G z) hGz
        simpa [Function.iterate_succ_apply] using hh
    intro z hz
    simp only [mem_iUnion] at hz
    obtain ⟨k, hk⟩ := hz
    exact ⟨k, hreachk k z hk⟩

/-- **The abstract spread-chain reduction.**  With `G` holomorphic on the open `D`, a covering of
`D` off `{0, v}`, `G 0 = 0`, `0` outside the parabolic basin of `G` on `D`, and petals `V i`:

if the critical value `v` is met by no level of the chain `spreadChain G D V`, then `G` maps each
level bijectively onto the previous one, the union `⋃ n, W n i` is simply connected, compact subsets
of it have compact preimages, it maps onto itself, and each of its points reaches `V i`.

Each level map is a covering of a simply connected base off the critical value, hence bijective and
a homeomorphism (`bijOn_and_isCompact_of_isCoveringMapOn`, `Work.BasinSC.simplyConnected_of_isCoveringMapOn`);
a loop in the increasing union is compact and so lies in one level, where it is null-homotopic; the
gluing lemmas of `spreadChain_union_structure_aux` turn the level-wise compactness and the
surjectivity into the corresponding statements for the union. -/
private theorem spreadChain_structure_aux {G : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {V : Fin q → Set ℂ}
    {v : ℂ}
    (hDopen : IsOpen D) (hGdiff : DifferentiableOn ℂ G D) (hG0 : G 0 = 0)
    (h0out : (0 : ℂ) ∉ MandelDim.ParabolicBasin G D)
    (hcov : IsCoveringMapOn (fun z : ↥D => G z) {ζ : ℂ | ζ ≠ 0 ∧ ζ ≠ v})
    (hcrit : ∀ z ∈ D, deriv G z = 0 → G z = v)
    (hVopen : ∀ i, IsOpen (V i)) (hVconn : ∀ i, IsConnected (V i)) (hVsub : ∀ i, V i ⊆ D)
    (hVmap : ∀ i, ∀ z ∈ V i, G z ∈ V i ∪ {0}) (hVne : ∀ i, (0 : ℂ) ∉ V i)
    (hVdisj : ∀ i j : Fin q, i ≠ j → Disjoint (V i) (V j)) (hVcl : ∀ i, (0 : ℂ) ∈ closure (V i))
    (hVsc : ∀ i, SimplyConnectedSpace (V i))
    (hVreach : ∀ z ∈ D, (∃ n : ℕ, (∀ k < n, G^[k] z ∈ D) ∧ G^[n] z ∈ ⋃ i, V i) →
      z ∈ MandelDim.ParabolicBasin G D) :
    ∀ (i : Fin q), v ∉ ⋃ n, spreadChain G D V n i →
      (∀ n : ℕ, Set.BijOn G (spreadChain G D V (n + 1) i) (spreadChain G D V n i)) ∧
      SimplyConnectedSpace (⋃ n, spreadChain G D V n i) ∧
      (∀ L : Set ℂ, L ⊆ ⋃ n, spreadChain G D V n i → IsCompact L →
        IsCompact ((⋃ n, spreadChain G D V n i) ∩ G ⁻¹' L)) ∧
      (⋃ n, spreadChain G D V n i) ⊆ G '' (⋃ n, spreadChain G D V n i) ∧
      (∀ z ∈ ⋃ n, spreadChain G D V n i, ∃ n : ℕ, (G^[n]) z ∈ V i) := by
  obtain ⟨hWopen, hWconn, hWsub, hW0, hWmono, hWmap, hWsat, _hWmax, _hWdisj⟩ :=
    spreadChain_props hDopen hGdiff hVopen hVconn hVsub hVmap hVne hVdisj hVcl h0out hVreach
  intro i hv
  have hv' : ∀ k : ℕ, v ∉ spreadChain G D V k i :=
    fun k h => hv (Set.mem_iUnion.mpr ⟨k, h⟩)
  -- `0` lies in no level of the chain
  have h0W : ∀ k : ℕ, (0 : ℂ) ∉ spreadChain G D V k i := by
    intro k
    induction k with
    | zero => rw [hW0 i]; exact hVne i
    | succ k ih =>
      intro h0
      exact ih (spreadChain_image_succ_subset (G := G) (D := D) (V := V) k i ⟨0, h0, hG0⟩)
  -- the covering of each level over the previous one, off the critical value
  have hlevelcov : ∀ k : ℕ,
      IsCoveringMapOn (fun z : ↥(spreadChain G D V (k + 1) i) => G z)
        (spreadChain G D V k i) := by
    intro k
    refine (spread_chain_covering_off_critval hDopen hGdiff hcov hcrit hWopen hWsub hWmono hWmap
      hWsat k i).mono ?_
    intro z hz
    exact ⟨hz, by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => h0W k (h ▸ hz), fun h => hv' k (h ▸ hz)⟩⟩
  -- the level structure, by induction on the level
  have hlevel : ∀ n : ℕ, SimplyConnectedSpace (spreadChain G D V n i) ∧
      Set.BijOn G (spreadChain G D V (n + 1) i) (spreadChain G D V n i) ∧
      (∀ L : Set ℂ, L ⊆ spreadChain G D V n i → IsCompact L →
        IsCompact (spreadChain G D V (n + 1) i ∩ G ⁻¹' L)) := by
    intro n
    induction n with
    | zero =>
      have hsc0 : SimplyConnectedSpace (spreadChain G D V 0 i) := by
        rw [hW0 i]; exact hVsc i
      obtain ⟨hbij0, hcomp0⟩ := bijOn_and_isCompact_of_isCoveringMapOn
        (G := G) (C := spreadChain G D V (0 + 1) i) (V := spreadChain G D V 0 i)
        (hWopen (0 + 1) i) (hWconn (0 + 1) i)
        (spreadChain_image_succ_subset (G := G) (D := D) (V := V) 0 i) hsc0 (hlevelcov 0)
      exact ⟨hsc0, hbij0, hcomp0⟩
    | succ n ih =>
      obtain ⟨hscn, hbijn, _hcompn⟩ := ih
      have hsc_succ : SimplyConnectedSpace (spreadChain G D V (n + 1) i) :=
        Work.BasinSC.simplyConnected_of_isCoveringMapOn
          (V := spreadChain G D V n i) (V' := spreadChain G D V (n + 1) i)
          (hWopen n i) (hWconn n i).nonempty hscn (hWopen (n + 1) i) (hWconn (n + 1) i)
          hbijn.mapsTo (hlevelcov n)
          (fun z hz => let ⟨w, hw, hwg⟩ := hbijn.2.2 hz; ⟨w, hw, hwg⟩)
      obtain ⟨hbij_succ, hcomp_succ⟩ := bijOn_and_isCompact_of_isCoveringMapOn
        (G := G) (C := spreadChain G D V (n + 1 + 1) i) (V := spreadChain G D V (n + 1) i)
        (hWopen (n + 1 + 1) i) (hWconn (n + 1 + 1) i)
        (spreadChain_image_succ_subset (G := G) (D := D) (V := V) (n + 1) i) hsc_succ
        (hlevelcov (n + 1))
      exact ⟨hsc_succ, hbij_succ, hcomp_succ⟩
  have hsc_all : ∀ n : ℕ, SimplyConnectedSpace (spreadChain G D V n i) := fun n => (hlevel n).1
  have hbij_all : ∀ n : ℕ, Set.BijOn G (spreadChain G D V (n + 1) i) (spreadChain G D V n i) :=
    fun n => (hlevel n).2.1
  have hcomp_all : ∀ n : ℕ, ∀ L : Set ℂ, L ⊆ spreadChain G D V n i → IsCompact L →
      IsCompact (spreadChain G D V (n + 1) i ∩ G ⁻¹' L) := fun n => (hlevel n).2.2
  obtain ⟨_hInj, hpre, honto, hreach⟩ :=
    spreadChain_union_structure_aux (G := G) (W := spreadChain G D V) i
      (fun n => hWmono n i) hbij_all
  refine ⟨hbij_all, ?_, ?_, honto, ?_⟩
  · -- the union is simply connected
    have hUopen : IsOpen (⋃ n, spreadChain G D V n i) := isOpen_iUnion (fun n => hWopen n i)
    have hUconn : IsConnected (⋃ n, spreadChain G D V n i) :=
      IsConnected.iUnion_of_chain (fun n => hWconn n i)
        (fun n => let ⟨x, hx⟩ := (hWconn n i).nonempty; ⟨x, hx, hWmono n i hx⟩)
    haveI : ConnectedSpace ↥(⋃ n, spreadChain G D V n i) :=
      isConnected_iff_connectedSpace.mp hUconn
    haveI : LocallyPathConnectedSpace ↥(⋃ n, spreadChain G D V n i) :=
      hUopen.locallyPathConnectedSpace
    haveI : PathConnectedSpace ↥(⋃ n, spreadChain G D V n i) :=
      PathConnectedSpace.of_locallyPathConnectedSpace
    refine (isSimplyConnected_iff_exists_homotopy_refl_forall_mem).mpr ⟨?_, ?_⟩
    · exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance
    · intro x p hp
      have hKc : IsCompact (Set.range p) := isCompact_range p.continuous
      have hKsub : Set.range p ⊆ ⋃ n, spreadChain G D V n i := by
        rintro z ⟨t, rfl⟩
        exact hp t
      obtain ⟨N, hN⟩ := exists_subset_of_isCompact_iUnion (fun n => hWopen n i)
        (fun n => hWmono n i) hKc hKsub
      obtain ⟨F, hF⟩ := (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp (hsc_all N)).2
        x p (fun t => hN (Set.mem_range_self t))
      exact ⟨F, fun t => Set.mem_iUnion.mpr ⟨N, hF t⟩⟩
  · -- compact preimages inside the union
    intro L hLsub hLc
    obtain ⟨N, hN⟩ := exists_subset_of_isCompact_iUnion (fun n => hWopen n i)
      (fun n => hWmono n i) hLc hLsub
    have hEq := hpre N
    have hset : (⋃ n, spreadChain G D V n i) ∩ G ⁻¹' L
        = spreadChain G D V (N + 1) i ∩ G ⁻¹' L := by
      apply Subset.antisymm
      · rintro z ⟨hzU, hzL⟩
        have h1 : z ∈ (⋃ m, spreadChain G D V m i) ∩ G ⁻¹' (spreadChain G D V N i) :=
          ⟨hzU, hN hzL⟩
        rw [hEq] at h1
        exact ⟨h1, hzL⟩
      · rintro z ⟨hz, hzL⟩
        exact ⟨Set.mem_iUnion.mpr ⟨N + 1, hz⟩, hzL⟩
    rw [hset]
    exact hcomp_all N L hN hLc
  · -- every point of the union reaches level `0`
    intro z hz
    obtain ⟨n, hn⟩ := hreach z hz
    exact ⟨n, by rw [hW0 i] at hn; exact hn⟩

theorem spreadChain_bijOn_structure {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hBne : B.Nonempty) {η : ℝ} {Bu Bl : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl)
    (c : ℂ) (hsetup : MandelDim.IsF0Setup f₀ D₀ B c)
    {q : ℕ} {V : Fin q → Set ℂ}
    (hVopen : ∀ i : Fin q, IsOpen (V i)) (hVconn : ∀ i : Fin q, IsConnected (V i))
    (hVsc : ∀ i : Fin q, SimplyConnectedSpace (V i))
    (hVsub : ∀ i : Fin q, V i ⊆ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))
    (hVmap : ∀ i : Fin q, ∀ z ∈ V i, MandelDim.pushdown d.E z ∈ V i ∪ {0})
    (hVne : ∀ i : Fin q, (0 : ℂ) ∉ V i)
    (hVdisj : ∀ i j : Fin q, i ≠ j → Disjoint (V i) (V j))
    (hVcl : ∀ i : Fin q, (0 : ℂ) ∈ closure (V i))
    (hVcapture : ∀ z ∈ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
        (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))),
      ∃ n : ℕ, (MandelDim.pushdown d.E)^[n] z ∈ ⋃ i, V i)
    (hVreach : ∀ z ∈ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)),
      (∃ n : ℕ, (∀ k < n, (MandelDim.pushdown d.E)^[k] z ∈
          insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) ∧
        (MandelDim.pushdown d.E)^[n] z ∈ ⋃ i, V i) →
      z ∈ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
        (insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))) :
    let W : ℕ → Fin q → Set ℂ := Work.Horn.spreadChain (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) V
    ∀ (i : Fin q), MandelDim.piExp (d.Φ c) ∉ ⋃ n, W n i →
      (∀ n : ℕ, Set.BijOn (MandelDim.pushdown d.E) (W (n + 1) i) (W n i)) ∧
      SimplyConnectedSpace (⋃ n, W n i) ∧
      (∀ L : Set ℂ, L ⊆ ⋃ n, W n i → IsCompact L →
        IsCompact ((⋃ n, W n i) ∩ (MandelDim.pushdown d.E) ⁻¹' L)) ∧
      (⋃ n, W n i) ⊆ (MandelDim.pushdown d.E) '' (⋃ n, W n i) ∧
      (∀ z ∈ ⋃ n, W n i, ∃ n : ℕ, (MandelDim.pushdown d.E)^[n] z ∈ V i) := by
  classical
  refine fun i hv => ?_
  -- the structural data of the pushed-down horn map on `D_g`
  obtain ⟨hBuO, hBlO, _hBuT, _hBlT, hup₀, hlo₀, _hDE⟩ :=
    horn_topo_facts hF0 d hB hBne hBu hBl hup hlo
  have hDopen : IsOpen (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) :=
    isOpen_insert_piExp hBuO hBlO hup hlo
  have hGdiff : DifferentiableOn ℂ (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) :=
    pushdown_g_holo hF0 d hB hBne hBu hBl hsub hup hlo
  have hG0 : MandelDim.pushdown d.E 0 = 0 := MandelDim.pushdown_zero d.E
  have h0out : (0 : ℂ) ∉ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) :=
    zero_not_mem_basin_pushdown hF0 d hB hBne hBu hBl hsub hup hlo
  have hcovE := cov_of_parts Work.HornTopo.horn_topo Work.HornPhi.horn_phi
    Work.HornVarphi.horn_varphi Work.Horn.hornSC f₀ D₀ B c d hsetup
  have hBuOf : Bu = MandelDim.BuOf d B := Bu_eq_BuOf d hBu hup hup₀
  have hBlOf : Bl = MandelDim.BlOf d B := Bl_eq_BlOf d hBl hlo hlo₀
  have hcov : IsCoveringMapOn
      (fun z : ↥(insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) => MandelDim.pushdown d.E z)
      {ζ : ℂ | ζ ≠ 0 ∧ ζ ≠ MandelDim.piExp (d.Φ c)} := by
    rw [hBuOf, hBlOf]
    exact pushdown_covering Work.HornTopo.horn_topo d hsetup hcovE
  have hcrit : ∀ z ∈ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)),
      deriv (MandelDim.pushdown d.E) z = 0 →
        MandelDim.pushdown d.E z = MandelDim.piExp (d.Φ c) :=
    pushdown_critval_global_eq hF0 d hB hBne hsetup hBu hBl hsub hup hlo
  exact spreadChain_structure_aux (G := MandelDim.pushdown d.E)
    (D := insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) (V := V) (v := MandelDim.piExp (d.Φ c))
    hDopen hGdiff hG0 h0out hcov hcrit hVopen hVconn hVsub hVmap hVne hVdisj hVcl hVsc hVreach
    i hv


end Work.Horn
