/-
  `Work.WilCrux.sep_or_lex` — the "same-base separation vs. lexicographic comparison" step of the
  isolation argument (node N1, `WilCrux/DESIGN.md`).

  Let `C` be a cylindrical decomposition of `ℝ^{m+N}` and let `κ ≠ κ'` be two of its cells whose
  projections onto `ℝ^m` are both the *same* set `C₀`.  Then either `κ` does not accumulate into
  `κ'` at all (`κ ∩ closure κ' = ∅`), or the type word of `κ` is lexicographically smaller than
  that of `κ'` (levels compared from the bottom up, `band > graph`).

  The proof is an induction on `N`.  Both cells project onto `C₀`, so their level-`(m+N-1)` bases
  `base κ`, `base κ'` are again cells of a cylindrical decomposition of `ℝ^{m+N-1}` projecting
  onto `C₀`, and the induction hypothesis applies to them:

  * if the bases differ and are separated, then so are `κ` and `κ'` (a point of `closure κ'`
    projects to a point of `closure (base κ')`, because `Fin.init` is continuous);
  * if the bases differ and `word (base κ) < word (base κ')`, the same witness of the prefix
    comparison shows `word κ < word κ'`, since `word m (N+1) κ = Fin.snoc (word m N (base κ))
    (levelType κ)`;
  * if the bases coincide, the words agree below the top level and the top level decides: if `κ`
    is a graph cell and `κ'` a band cell over the common base, then `word κ < word κ'`; in every
    other case (`κ` a band, or `κ'` a graph) a common-base separation lemma (`levelSepAux`, built
    from the closure descriptions of graph and band cells) shows that the closures are disjoint.
-/
import Mathlib
import Submission.Work.WilCrux.SheetDefs
import Submission.Work.WilCrux.isCell_level_data

set_option autoImplicit false
noncomputable section
open Classical
open Filter
open scoped Topology

namespace Work.WilCrux

/-! ## 0. Elementary topological and order-theoretic helpers -/

/-- `Fin.init` is continuous. -/
private theorem continuous_init_fin (n : ℕ) :
    Continuous (Fin.init : (Fin (n + 1) → ℝ) → Fin n → ℝ) :=
  continuous_pi fun (i : Fin n) => continuous_apply (Fin.castSucc i)

/-- The projection of the closure is contained in the closure of the projection. -/
private theorem init_image_closure_subset {p : ℕ} (A : Set (Fin (p + 1) → ℝ)) :
    Fin.init '' closure A ⊆ closure (Fin.init '' A) :=
  image_closure_subset_closure_image (continuous_init_fin p)

/-- If `Fin.init '' A` is separated from the closure of `Fin.init '' B`, then `A` is separated
from the closure of `B`. -/
private theorem inter_closure_empty_of_base {p : ℕ} {A B : Set (Fin (p + 1) → ℝ)}
    (h : Fin.init '' A ∩ closure (Fin.init '' B) = ∅) : A ∩ closure B = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem] at h ⊢
  intro z hz
  exact h (Fin.init z) ⟨⟨z, hz.1, rfl⟩, init_image_closure_subset B ⟨z, hz.2, rfl⟩⟩

/-- `LexLt` is preserved by appending a further level. -/
private theorem lexLt_snoc_lift {N : ℕ} {u v : Fin N → CellType} (h : LexLt u v)
    (a b : CellType) : LexLt (Fin.snoc u a) (Fin.snoc v b) := by
  obtain ⟨j, hu, hv, hag⟩ := h
  refine ⟨j.castSucc, ?_, ?_, ?_⟩
  · rw [Fin.snoc_castSucc]; exact hu
  · rw [Fin.snoc_castSucc]; exact hv
  · intro i hi
    rcases Fin.eq_castSucc_or_eq_last i with ⟨k, rfl⟩ | hlast
    · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact hag k (Fin.castSucc_lt_castSucc_iff.mp hi)
    · rw [hlast] at hi
      exact absurd hi (not_lt.mpr (Fin.le_last j.castSucc))

/-- Appending a *graph* level above a *band* level (to the same prefix) makes a strictly smaller
type word. -/
private theorem lexLt_snoc_graph_band {N : ℕ} (u : Fin N → CellType) :
    LexLt (Fin.snoc u CellType.graph) (Fin.snoc u CellType.band) := by
  refine ⟨Fin.last N, ?_, ?_, ?_⟩
  · rw [Fin.snoc_last]
  · rw [Fin.snoc_last]
  · intro i hi
    rcases Fin.eq_castSucc_or_eq_last i with ⟨k, rfl⟩ | hlast
    · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
    · rw [hlast] at hi
      exact absurd hi (not_lt.mpr (Fin.le_last (Fin.last N)))

/-- The top level of `κ` is a graph level exactly when `κ` is a graph cell. -/
private theorem levelType_eq_graph_iff {p : ℕ} (κ : Set (Fin (p + 1) → ℝ)) :
    levelType κ = CellType.graph ↔ IsGraphCellAt κ (base κ) := by
  by_cases h : IsGraphCellAt κ (base κ) <;> simp [levelType, h]

/-- The top level of `κ` is a band level exactly when `κ` is not a graph cell. -/
private theorem levelType_eq_band_iff {p : ℕ} (κ : Set (Fin (p + 1) → ℝ)) :
    levelType κ = CellType.band ↔ ¬ IsGraphCellAt κ (base κ) := by
  by_cases h : IsGraphCellAt κ (base κ) <;> simp [levelType, h]

/-! ## 1. Closure descriptions of a graph cell and a band cell -/

/-- A graph cell over `D` does not leave the graph at a `D`-point of its closure. -/
private theorem graph_closure_mem {p : ℕ} {D : Set (Fin p → ℝ)} {g : (Fin p → ℝ) → ℝ}
    (hg : ContinuousOn g D) {z : Fin (p + 1) → ℝ}
    (hz : z ∈ closure {w : Fin (p + 1) → ℝ |
      Fin.init w ∈ D ∧ w (Fin.last p) = g (Fin.init w)})
    (hxD : Fin.init z ∈ D) :
    z (Fin.last p) = g (Fin.init z) := by
  obtain ⟨w, hw, hwtend⟩ := mem_closure_iff_seq_limit.mp hz
  have hinit : Tendsto (fun n => Fin.init (w n)) atTop (𝓝 (Fin.init z)) :=
    (continuous_init_fin p).tendsto z |>.comp hwtend
  have hwithin : Tendsto (fun n => Fin.init (w n)) atTop (𝓝[D] (Fin.init z)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hinit, Filter.Eventually.of_forall fun n => (hw n).1⟩
  have hg_tend : Tendsto (fun n => g (Fin.init (w n))) atTop (𝓝 (g (Fin.init z))) :=
    (show Tendsto g (𝓝[D] (Fin.init z)) (𝓝 (g (Fin.init z))) from
      hg (Fin.init z) hxD).comp hwithin
  have hlast : Tendsto (fun n => w n (Fin.last p)) atTop (𝓝 (z (Fin.last p))) :=
    ((continuous_apply (Fin.last p)).tendsto z).comp hwtend
  have heq : (fun n => w n (Fin.last p)) = fun n => g (Fin.init (w n)) :=
    funext fun n => (hw n).2
  rw [heq] at hlast
  exact tendsto_nhds_unique hlast hg_tend

/-- A band cell over `D` stays inside the *closed* band at a `D`-point of its closure. -/
private theorem band_closure_bounds {p : ℕ} {D : Set (Fin p → ℝ)} {a b : (Fin p → ℝ) → EReal}
    (ha : ContinuousOn a D) (hb : ContinuousOn b D) {z : Fin (p + 1) → ℝ}
    (hz : z ∈ closure {w : Fin (p + 1) → ℝ | Fin.init w ∈ D ∧
      a (Fin.init w) < ((w (Fin.last p) : ℝ) : EReal) ∧
      ((w (Fin.last p) : ℝ) : EReal) < b (Fin.init w)})
    (hxD : Fin.init z ∈ D) :
    a (Fin.init z) ≤ ((z (Fin.last p) : ℝ) : EReal) ∧
      ((z (Fin.last p) : ℝ) : EReal) ≤ b (Fin.init z) := by
  obtain ⟨w, hw, hwtend⟩ := mem_closure_iff_seq_limit.mp hz
  have hinit : Tendsto (fun n => Fin.init (w n)) atTop (𝓝 (Fin.init z)) :=
    (continuous_init_fin p).tendsto z |>.comp hwtend
  have hwithin : Tendsto (fun n => Fin.init (w n)) atTop (𝓝[D] (Fin.init z)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hinit, Filter.Eventually.of_forall fun n => (hw n).1⟩
  have ha_tend : Tendsto (fun n => a (Fin.init (w n))) atTop (𝓝 (a (Fin.init z))) :=
    (show Tendsto a (𝓝[D] (Fin.init z)) (𝓝 (a (Fin.init z))) from
      ha (Fin.init z) hxD).comp hwithin
  have hb_tend : Tendsto (fun n => b (Fin.init (w n))) atTop (𝓝 (b (Fin.init z))) :=
    (show Tendsto b (𝓝[D] (Fin.init z)) (𝓝 (b (Fin.init z))) from
      hb (Fin.init z) hxD).comp hwithin
  have hwlast : Tendsto (fun n => w n (Fin.last p)) atTop (𝓝 (z (Fin.last p))) :=
    ((continuous_apply (Fin.last p)).tendsto z).comp hwtend
  have hcoe : Tendsto (fun n => ((w n (Fin.last p) : ℝ) : EReal)) atTop
      (𝓝 (((z (Fin.last p) : ℝ) : EReal))) :=
    continuous_coe_real_ereal.tendsto _ |>.comp hwlast
  exact ⟨le_of_tendsto_of_tendsto' ha_tend hcoe (fun n => le_of_lt (hw n).2.1),
         le_of_tendsto_of_tendsto' hcoe hb_tend (fun n => le_of_lt (hw n).2.2)⟩

/-! ## 2. Two disjoint graph/band cells over a common base -/

/-- A real `y` lying strictly inside the open interval `(a,b)` of `EReal` cannot also lie in the
closed interval `[a',b']` when the two *open* intervals have no common real point. -/
private theorem ereal_band_disjoint {a b a' b' : EReal} (hab' : a' < b')
    (hdisj : ∀ t : ℝ, ¬ (a < (t : EReal) ∧ (t : EReal) < b ∧
      a' < (t : EReal) ∧ (t : EReal) < b'))
    {y : ℝ} (ha : a < (y : EReal)) (hb : (y : EReal) < b)
    (ha' : a' ≤ (y : EReal)) (hb' : (y : EReal) ≤ b') : False := by
  rcases lt_or_eq_of_le ha' with h1 | h1
  · rcases lt_or_eq_of_le hb' with h2 | h2
    · exact hdisj y ⟨ha, hb, h1, h2⟩
    · obtain ⟨t, ht1, ht2⟩ :=
        EReal.lt_iff_exists_real_btwn.mp (max_lt_iff.mpr ⟨ha, h1⟩)
      exact hdisj t ⟨lt_of_le_of_lt (le_max_left a a') ht1, lt_trans ht2 hb,
        lt_of_le_of_lt (le_max_right a a') ht1, h2 ▸ ht2⟩
  · rcases lt_or_eq_of_le hb' with h2 | h2
    · obtain ⟨t, ht1, ht2⟩ :=
        EReal.lt_iff_exists_real_btwn.mp (lt_min_iff.mpr ⟨hb, h2⟩)
      exact hdisj t ⟨lt_trans ha ht1, lt_of_lt_of_le ht2 (min_le_left b b'),
        h1.symm ▸ ht1, lt_of_lt_of_le ht2 (min_le_right b b')⟩
    · exact absurd (h1.trans h2) (ne_of_lt hab')

/-- Two disjoint cells of `ℝ^{p+1}` over the *same* base `D`, each of them a graph cell or a band
cell, cannot have a point of the first in the closure of the second — unless the first is a graph
and the second a band (the excluded case `hnot`; that case really does occur, e.g. the isolated
point `{0}` and the interval `(0,1)` over the base `D = {0}`, whose closure contains `0`). -/
private theorem levelSepAux {p : ℕ} {D : Set (Fin p → ℝ)} {A A' : Set (Fin (p + 1) → ℝ)}
    (hA : IsGraphCellAt A D ∨ IsBandCellAt A D)
    (hA' : IsGraphCellAt A' D ∨ IsBandCellAt A' D)
    (hdisj : Disjoint A A')
    (hnot : ¬ (IsGraphCellAt A D ∧ IsBandCellAt A' D)) :
    A ∩ closure A' = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro z hz
  rw [Set.mem_inter_iff] at hz
  obtain ⟨hzA, hzcl⟩ := hz
  rcases hA with hAg | hAb
  · rcases hA' with hA'g | hA'b
    · obtain ⟨f, hf, rfl⟩ := hAg
      obtain ⟨g, hg, rfl⟩ := hA'g
      have hxD : Fin.init z ∈ D := hzA.1
      have hlast : z (Fin.last p) = g (Fin.init z) := graph_closure_mem hg hzcl hxD
      exact Set.disjoint_left.mp hdisj hzA ⟨hxD, hlast⟩
    · exact absurd ⟨hAg, hA'b⟩ hnot
  · rcases hA' with hA'g | hA'b
    · obtain ⟨a, b, ha, hb, hab, rfl⟩ := hAb
      obtain ⟨g, hg, rfl⟩ := hA'g
      have hxD : Fin.init z ∈ D := hzA.1
      have hlast : z (Fin.last p) = g (Fin.init z) := graph_closure_mem hg hzcl hxD
      exact Set.disjoint_left.mp hdisj hzA ⟨hxD, hlast⟩
    · obtain ⟨a, b, ha, hb, hab, rfl⟩ := hAb
      obtain ⟨a', b', ha', hb', hab', rfl⟩ := hA'b
      have hxD : Fin.init z ∈ D := hzA.1
      obtain ⟨hle, hge⟩ := band_closure_bounds ha' hb' hzcl hxD
      refine ereal_band_disjoint (hab' (Fin.init z) hxD) ?_ hzA.2.1 hzA.2.2 hle hge
      intro t ht
      obtain ⟨h1, h2, h3, h4⟩ := ht
      have hmemA : Fin.snoc (Fin.init z) t ∈ {w : Fin (p + 1) → ℝ | Fin.init w ∈ D ∧
          a (Fin.init w) < ((w (Fin.last p) : ℝ) : EReal) ∧
          ((w (Fin.last p) : ℝ) : EReal) < b (Fin.init w)} :=
        ⟨by rw [Fin.init_snoc]; exact hxD, by rw [Fin.init_snoc, Fin.snoc_last]; exact h1,
          by rw [Fin.init_snoc, Fin.snoc_last]; exact h2⟩
      have hmemB : Fin.snoc (Fin.init z) t ∈ {w : Fin (p + 1) → ℝ | Fin.init w ∈ D ∧
          a' (Fin.init w) < ((w (Fin.last p) : ℝ) : EReal) ∧
          ((w (Fin.last p) : ℝ) : EReal) < b' (Fin.init w)} :=
        ⟨by rw [Fin.init_snoc]; exact hxD, by rw [Fin.init_snoc, Fin.snoc_last]; exact h3,
          by rw [Fin.init_snoc, Fin.snoc_last]; exact h4⟩
      exact Set.disjoint_left.mp hdisj hmemA hmemB

/-- A set cannot be at the same time a graph cell and a band cell over a nonempty base. -/
private theorem graph_band_exclusive {p : ℕ} {D : Set (Fin p → ℝ)} {A : Set (Fin (p + 1) → ℝ)}
    (hD : D.Nonempty) (hg : IsGraphCellAt A D) (hb : IsBandCellAt A D) : False := by
  obtain ⟨f, hf, hA⟩ := hg
  obtain ⟨a, b, ha, hb', hab, hA'⟩ := hb
  obtain ⟨x, hx⟩ := hD
  have hfx : a x < ((f x : ℝ) : EReal) ∧ ((f x : ℝ) : EReal) < b x := by
    have hmem : Fin.snoc x (f x) ∈ A := by
      rw [hA]
      exact ⟨by rw [Fin.init_snoc]; exact hx, by rw [Fin.init_snoc, Fin.snoc_last]⟩
    have hmem' : Fin.snoc x (f x) ∈ {z : Fin (p + 1) → ℝ | Fin.init z ∈ D ∧
        a (Fin.init z) < ((z (Fin.last p) : ℝ) : EReal) ∧
        ((z (Fin.last p) : ℝ) : EReal) < b (Fin.init z)} := hA' ▸ hmem
    obtain ⟨-, h1, h2⟩ := hmem'
    rw [Fin.init_snoc, Fin.snoc_last] at h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨t, ht1, ht2⟩ := EReal.exists_between_coe_real hfx.1
  have hmem2 : Fin.snoc x t ∈ A := by
    rw [hA']
    exact ⟨by rw [Fin.init_snoc]; exact hx, by rw [Fin.init_snoc, Fin.snoc_last]; exact ht1,
      by rw [Fin.init_snoc, Fin.snoc_last]; exact lt_trans ht2 hfx.2⟩
  rw [hA] at hmem2
  obtain ⟨-, heq⟩ := hmem2
  rw [Fin.init_snoc, Fin.snoc_last] at heq
  have hlt' : t < f x := EReal.coe_lt_coe_iff.mp ht2
  exact absurd heq (ne_of_lt hlt')

/-! ## 3. The induction on the number of levels -/

set_option linter.unusedVariables false in
theorem sep_or_lex {m N : ℕ} {C : Finset (Set (Fin (m + N) → ℝ))}
    (hdec : WilkiesDesign.IsCylDecomp (m + N) C) {C₀ : Set (Fin m → ℝ)} (hC₀ : IsOpen C₀)
    {κ κ' : Set (Fin (m + N) → ℝ)} (hκ : κ ∈ C) (hκ' : κ' ∈ C)
    (hO : Work.WilCrux.projOver m N κ = C₀) (hO' : Work.WilCrux.projOver m N κ' = C₀)
    (hne : κ ≠ κ') :
    κ ∩ closure κ' = ∅ ∨
      Work.WilCrux.LexLt (Work.WilCrux.word m N κ) (Work.WilCrux.word m N κ') := by
  induction N with
  | zero =>
      -- `κ = projOver m 0 κ = C₀ = projOver m 0 κ' = κ'`, contradicting `hne`
      exact absurd (hO.trans hO'.symm) hne
  | succ N ih =>
      -- the pieces of `IsCylDecomp (m + (N+1)) C`
      obtain ⟨hcells, hpd, -, hdec'⟩ : (∀ c ∈ C, WilkiesDesign.IsCell (m + (N + 1)) c ∧ c.Nonempty) ∧
          (↑C : Set (Set (Fin (m + (N + 1)) → ℝ))).PairwiseDisjoint id ∧
          (∀ z : Fin (m + (N + 1)) → ℝ, ∃ c ∈ C, z ∈ c) ∧
          WilkiesDesign.IsCylDecomp (m + N) (C.image (fun c => Fin.init '' c)) := by
        have h' : WilkiesDesign.IsCylDecomp (Nat.succ (m + N)) C := hdec
        rw [WilkiesDesign.IsCylDecomp.eq_2] at h'
        exact h'
      -- both bases still project onto `C₀`
      have hObase : projOver m N (base κ) = C₀ := hO
      have hO'base : projOver m N (base κ') = C₀ := hO'
      by_cases hbase : base κ = base κ'
      · -- same base: the top level decides
        have hneκ : κ.Nonempty := (hcells κ hκ).2
        obtain ⟨-, hDne, hgbκ⟩ := isCell_level_data (hcells κ hκ).1 hneκ
        obtain ⟨-, -, hgbκ'⟩ := isCell_level_data (hcells κ' hκ').1 (hcells κ' hκ').2
        have hgbκ'D : IsGraphCellAt κ' (base κ) ∨ IsBandCellAt κ' (base κ) := by
          rw [hbase]; exact hgbκ'
        have hdisj : Disjoint κ κ' := hpd hκ hκ' hne
        by_cases hgκ : IsGraphCellAt κ (base κ)
        · by_cases hgκ' : IsGraphCellAt κ' (base κ')
          · -- both are graphs: the closures are disjoint
            have hgκ'D : IsGraphCellAt κ' (base κ) := by rw [hbase]; exact hgκ'
            left
            exact levelSepAux hgbκ hgbκ'D hdisj
              (fun hcon => graph_band_exclusive hDne hgκ'D hcon.2)
          · -- graph below band at the top level: `word κ` is lexicographically smaller
            right
            rw [word_succ, word_succ, ← hbase]
            rw [(levelType_eq_graph_iff κ).2 hgκ, (levelType_eq_band_iff κ').2 hgκ']
            exact lexLt_snoc_graph_band (word m N (base κ))
        · -- `κ` is a band at the top level: the closures are disjoint
          left
          exact levelSepAux hgbκ hgbκ'D hdisj (fun hcon => hgκ hcon.1)
      · -- different bases: apply the induction hypothesis to the bases
        rcases ih hdec' (Finset.mem_image.mpr ⟨κ, hκ, rfl⟩) (Finset.mem_image.mpr ⟨κ', hκ', rfl⟩)
          hObase hO'base hbase with hsep | hlex
        · left
          exact inter_closure_empty_of_base hsep
        · right
          rw [word_succ, word_succ]
          exact lexLt_snoc_lift hlex (levelType κ) (levelType κ')

end Work.WilCrux
