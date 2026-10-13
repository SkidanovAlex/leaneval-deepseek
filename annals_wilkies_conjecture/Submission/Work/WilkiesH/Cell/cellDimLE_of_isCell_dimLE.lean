import Mathlib
import Submission.Work.WilkiesH.Cell
import Submission.Work.WilkiesH.Basic

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkiesH.Cell

open WilkiesDesign

/-- `Fin.snoc` with the codomain pinned to `ℝ`, avoiding dependent-type inference issues. -/
abbrev snocR {n : ℕ} (p : Fin n → ℝ) (x : ℝ) : Fin (n + 1) → ℝ := Fin.snoc p x

@[simp] theorem snocR_castSucc {n : ℕ} (p : Fin n → ℝ) (x : ℝ) (i : Fin n) :
    snocR p x (Fin.castSucc i) = p i := Fin.snoc_castSucc _ _ _

@[simp] theorem snocR_last {n : ℕ} (p : Fin n → ℝ) (x : ℝ) : snocR p x (Fin.last n) = x :=
  Fin.snoc_last _ _

theorem snocR_init_self {n : ℕ} (q : Fin (n + 1) → ℝ) :
    snocR (Fin.init q) (q (Fin.last n)) = q := Fin.snoc_init_self q

theorem init_snocR {n : ℕ} (p : Fin n → ℝ) (x : ℝ) : Fin.init (snocR p x) = p := by
  funext i
  show snocR p x (Fin.castSucc i) = p i
  rw [snocR_castSucc]

/-- The embedding of the first coordinates obtained by adjoining one graph coordinate. -/
def succEmb {n : ℕ} : Fin n ↪ Fin (n + 1) := ⟨Fin.castSucc, Fin.castSucc_injective n⟩

/-- The projection of `C ⊆ ℝⁿ` onto the coordinates selected by an embedding `e : Fin m ↪ Fin n`. -/
def ProjE {m n : ℕ} (e : Fin m ↪ Fin n) (C : Set (Fin n → ℝ)) : Set (Fin m → ℝ) :=
  (fun x => x ∘ e) '' C

/-- Band-chart data for a cell: `e` indexes the band coordinates, `ProjE e C` is open, and
`Φ` is a continuous section of `ProjE e` which is a genuine two-sided inverse on `C`. -/
def Good (n : ℕ) (C : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (e : Fin m ↪ Fin n) (Φ : (Fin m → ℝ) → (Fin n → ℝ)),
    CellDimLE n C m ∧ IsOpen (ProjE e C) ∧ ContinuousOn Φ (ProjE e C) ∧
    (∀ x ∈ C, Φ (x ∘ e) = x) ∧
    (∀ u ∈ ProjE e C, Φ u ∘ e = u)

/-- Every cell is nonempty. -/
theorem isCell_nonempty {n : ℕ} {C : Set (Fin n → ℝ)} (h : IsCell n C) : C.Nonempty := by
  induction h with
  | zero => exact ⟨Fin.elim0, Set.mem_univ _⟩
  | graph hC f hf ih =>
      obtain ⟨y, hy⟩ := ih
      refine ⟨snocR y (f y), ?_, ?_⟩
      · rw [init_snocR]; exact hy
      · rw [snocR_last, init_snocR]
  | band hC a b ha hb hab ih =>
      obtain ⟨y, hy⟩ := ih
      obtain ⟨t, ht1, ht2⟩ := EReal.lt_iff_exists_real_btwn.mp (hab y hy)
      refine ⟨snocR y t, ?_, ?_, ?_⟩
      · rw [init_snocR]; exact hy
      · rw [init_snocR, snocR_last]; exact ht1
      · rw [init_snocR, snocR_last]; exact ht2

/-- The embedding of the band coordinates obtained by adjoining one further band coordinate. -/
def bandEmb {m n : ℕ} (e₀ : Fin m ↪ Fin n) : Fin (m + 1) ↪ Fin (n + 1) :=
  ⟨Fin.snoc (α := fun _ => Fin (n + 1)) (fun i => Fin.castSucc (e₀ i)) (Fin.last n), by
    intro i j hij
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · rw [Fin.snoc_castSucc] at hij
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · rw [Fin.snoc_castSucc] at hij
        exact congrArg Fin.castSucc (e₀.injective (Fin.castSucc_injective _ hij))
      · rw [Fin.snoc_last] at hij
        exact absurd hij (ne_of_lt (Fin.castSucc_lt_last _))
    · rw [Fin.snoc_last] at hij
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · rw [Fin.snoc_castSucc] at hij
        exact absurd hij.symm (ne_of_lt (Fin.castSucc_lt_last _))
      · rfl⟩

@[simp] theorem bandEmb_castSucc {m n : ℕ} (e₀ : Fin m ↪ Fin n) (i : Fin m) :
    bandEmb e₀ (Fin.castSucc i) = Fin.castSucc (e₀ i) := by
  show Fin.snoc (α := fun _ => Fin (n + 1)) (fun i => Fin.castSucc (e₀ i)) (Fin.last n)
      (Fin.castSucc i) = _
  rw [Fin.snoc_castSucc]

@[simp] theorem bandEmb_last {m n : ℕ} (e₀ : Fin m ↪ Fin n) :
    bandEmb e₀ (Fin.last m) = Fin.last n := by
  show Fin.snoc (α := fun _ => Fin (n + 1)) (fun i => Fin.castSucc (e₀ i)) (Fin.last n)
      (Fin.last m) = _
  rw [Fin.snoc_last]

/-- A point of `ℝ^{n+1}` composed with the band embedding. -/
theorem comp_bandEmb {m n : ℕ} (e₀ : Fin m ↪ Fin n) (z : Fin (n + 1) → ℝ) :
    z ∘ (bandEmb e₀) = snocR ((Fin.init z) ∘ e₀) (z (Fin.last n)) := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
  · rw [Function.comp_apply, bandEmb_castSucc, snocR_castSucc]; rfl
  · rw [Function.comp_apply, bandEmb_last, snocR_last]

theorem init_comp_bandEmb {m n : ℕ} (e₀ : Fin m ↪ Fin n) (z : Fin (n + 1) → ℝ) :
    Fin.init (z ∘ (bandEmb e₀)) = (Fin.init z) ∘ e₀ := by
  rw [comp_bandEmb, init_snocR]

theorem comp_graphEmb {m n : ℕ} (e₀ : Fin m ↪ Fin n) (z : Fin (n + 1) → ℝ) :
    z ∘ (e₀.trans succEmb) = (Fin.init z) ∘ e₀ := by
  funext i
  rfl

/-- Every cell admits band-chart data. -/
theorem good_of_isCell {n : ℕ} {C : Set (Fin n → ℝ)} (h : IsCell n C) : Good n C := by
  refine IsCell.rec (motive := fun n C _ => Good n C) ?_ ?_ ?_ h
  · -- zero
    refine ⟨0, (Equiv.refl (Fin 0)).toEmbedding, id, CellDimLE.zero, ?_, ?_, ?_, ?_⟩
    · have hh : ProjE (Equiv.refl (Fin 0)).toEmbedding (Set.univ : Set (Fin 0 → ℝ)) = Set.univ := by
        rw [ProjE, Set.image_univ, Set.range_eq_univ]
        exact fun y => ⟨y, Subsingleton.elim _ _⟩
      rw [hh]; exact isOpen_univ
    · exact continuous_id.continuousOn
    · intro x _
      exact Subsingleton.elim _ _
    · intro u _
      exact Subsingleton.elim _ _
  · -- graph
    intro n C hC f hf ih
    obtain ⟨m, e₀, Φ₀, hcell, hopen, hcont, hleft, hright⟩ := ih
    have hinit : Continuous (Fin.init : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) :=
      continuous_pi fun i => continuous_apply _
    have hΦmaps : Set.MapsTo Φ₀ (ProjE e₀ C) C := fun u hu => by
      obtain ⟨x, hx, hxu⟩ := hu
      rw [← hxu, hleft x hx]; exact hx
    have hset : ProjE (e₀.trans succEmb)
        {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧ z (Fin.last n) = f (Fin.init z)}
        = ProjE e₀ C := by
      ext u
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨Fin.init z, hz.1, (comp_graphEmb e₀ z).symm⟩
      · rintro ⟨y, hy, rfl⟩
        refine ⟨snocR y (f y), ⟨?_, ?_⟩, ?_⟩
        · rw [init_snocR]; exact hy
        · rw [snocR_last, init_snocR]
        · simp only [comp_graphEmb, init_snocR]
    refine ⟨m, e₀.trans succEmb,
      (fun u => snocR (Φ₀ u) (f (Φ₀ u))), CellDimLE.graph hcell f hf, ?_, ?_, ?_, ?_⟩
    · rw [hset]; exact hopen
    · rw [hset, continuousOn_pi]
      intro j
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · exact ((continuousOn_pi.mp hcont) j').congr (fun u _ => by rw [snocR_castSucc])
      · exact (hf.comp hcont hΦmaps).congr (fun u _ => by rw [snocR_last, Function.comp_apply])
    · intro z hz
      dsimp only
      rw [show Φ₀ (z ∘ (e₀.trans succEmb)) = Fin.init z
          from by rw [comp_graphEmb]; exact hleft (Fin.init z) hz.1]
      rw [← hz.2]
      exact snocR_init_self z
    · intro u hu
      funext i
      show snocR (Φ₀ u) (f (Φ₀ u)) (Fin.castSucc (e₀ i)) = u i
      rw [snocR_castSucc]
      exact congrFun (hright u (hset ▸ hu)) i
  · -- band
    intro n C hC a b ha hb hab ih
    obtain ⟨m, e₀, Φ₀, hcell, hopen, hcont, hleft, hright⟩ := ih
    have hΦmaps : Set.MapsTo Φ₀ (ProjE e₀ C) C := fun u hu => by
      obtain ⟨x, hx, hxu⟩ := hu
      rw [← hxu, hleft x hx]; exact hx
    have hinit : Continuous (Fin.init : (Fin (m + 1) → ℝ) → (Fin m → ℝ)) :=
      continuous_pi fun i => continuous_apply _
    have hset : ProjE (bandEmb e₀)
        {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧ a (Fin.init z) < ↑(z (Fin.last n)) ∧
          ↑(z (Fin.last n)) < b (Fin.init z)}
        = {w : Fin (m + 1) → ℝ | Fin.init w ∈ ProjE e₀ C ∧
            a (Φ₀ (Fin.init w)) < ↑(w (Fin.last m)) ∧
            ↑(w (Fin.last m)) < b (Φ₀ (Fin.init w))} := by
      ext w
      constructor
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨hz1, hz2, hz3⟩ := hz
        refine ⟨⟨Fin.init z, hz1, (init_comp_bandEmb e₀ z).symm⟩, ?_, ?_⟩
        · rw [init_comp_bandEmb, hleft (Fin.init z) hz1]
          simpa [Function.comp_apply] using hz2
        · rw [init_comp_bandEmb, hleft (Fin.init z) hz1]
          simpa [Function.comp_apply] using hz3
      · rintro ⟨hu, h1, h2⟩
        obtain ⟨y, hy, hyu⟩ := hu
        have hyu' : y ∘ e₀ = Fin.init w := hyu
        have hyw : Φ₀ (Fin.init w) = y := by rw [← hyu', hleft y hy]
        have hyw' : Φ₀ (Fin.init w) = y := hyw
        refine ⟨snocR y (w (Fin.last m)), ⟨?_, ?_, ?_⟩, ?_⟩
        · rw [init_snocR]; exact hy
        · rw [init_snocR, snocR_last, ← hyw']; exact h1
        · rw [init_snocR, snocR_last, ← hyw']; exact h2
        · dsimp only
          rw [comp_bandEmb, init_snocR, snocR_last, hyu']
          exact snocR_init_self w
    refine ⟨m + 1, bandEmb e₀, (fun u => snocR (Φ₀ (Fin.init u)) (u (Fin.last m))),
      CellDimLE.band hcell a b ha hb hab, ?_, ?_, ?_, ?_⟩
    · rw [hset]
      set U := ProjE e₀ C with hUdef
      set F : (Fin (m + 1) → ℝ) → EReal := fun w => a (Φ₀ (Fin.init w))
      set F' : (Fin (m + 1) → ℝ) → EReal := fun w => b (Φ₀ (Fin.init w))
      set G : (Fin (m + 1) → ℝ) → EReal := fun w => ↑(w (Fin.last m))
      have hV : IsOpen {w : Fin (m + 1) → ℝ | Fin.init w ∈ U} := hopen.preimage hinit
      have hFcont : ContinuousOn F {w : Fin (m + 1) → ℝ | Fin.init w ∈ U} :=
        (ha.comp hcont hΦmaps).comp hinit.continuousOn (fun w hw => hw)
      have hF'cont : ContinuousOn F' {w : Fin (m + 1) → ℝ | Fin.init w ∈ U} :=
        (hb.comp hcont hΦmaps).comp hinit.continuousOn (fun w hw => hw)
      have hGcont : ContinuousOn G {w : Fin (m + 1) → ℝ | Fin.init w ∈ U} :=
        (continuous_coe_real_ereal.comp (continuous_apply (Fin.last m))).continuousOn
      have hlt : IsOpen {p : EReal × EReal | p.1 < p.2} :=
        isOpen_lt continuous_fst continuous_snd
      have h1 : IsOpen ({w : Fin (m + 1) → ℝ | Fin.init w ∈ U} ∩
          (fun w => (F w, G w)) ⁻¹' {p : EReal × EReal | p.1 < p.2}) :=
        ContinuousOn.isOpen_inter_preimage (hFcont.prodMk hGcont) hV hlt
      have h2 : IsOpen ({w : Fin (m + 1) → ℝ | Fin.init w ∈ U} ∩
          (fun w => (G w, F' w)) ⁻¹' {p : EReal × EReal | p.1 < p.2}) :=
        ContinuousOn.isOpen_inter_preimage (hGcont.prodMk hF'cont) hV hlt
      have hfinal : {w : Fin (m + 1) → ℝ | Fin.init w ∈ U ∧ F w < G w ∧ G w < F' w}
          = ({w : Fin (m + 1) → ℝ | Fin.init w ∈ U} ∩
              (fun w => (F w, G w)) ⁻¹' {p : EReal × EReal | p.1 < p.2}) ∩
            ({w : Fin (m + 1) → ℝ | Fin.init w ∈ U} ∩
              (fun w => (G w, F' w)) ⁻¹' {p : EReal × EReal | p.1 < p.2}) := by
        ext w
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
        tauto
      rw [hfinal]
      exact h1.inter h2
    · rw [hset, continuousOn_pi]
      intro j
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · exact (((continuousOn_pi.mp hcont) j').comp hinit.continuousOn
            (fun w hw => hw.1)).congr (fun u _ => by rw [snocR_castSucc, Function.comp_apply])
      · exact ((continuous_apply (Fin.last m)).continuousOn).congr
            (fun u _ => by rw [snocR_last])
    · intro z hz
      obtain ⟨hz1, hz2, hz3⟩ := hz
      dsimp only
      rw [init_comp_bandEmb, hleft (Fin.init z) hz1, Function.comp_apply, bandEmb_last]
      exact snocR_init_self z
    · intro u hu
      have hinit_u : Fin.init u ∈ ProjE e₀ C := by
        rw [hset] at hu
        exact hu.1
      funext i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · rw [Function.comp_apply, bandEmb_castSucc]
        show snocR (Φ₀ (Fin.init u)) (u (Fin.last m)) (Fin.castSucc (e₀ i'))
              = u (Fin.castSucc i')
        rw [snocR_castSucc]
        exact congrFun (hright (Fin.init u) hinit_u) i'
      · rw [Function.comp_apply, bandEmb_last]
        show snocR (Φ₀ (Fin.init u)) (u (Fin.last m)) (Fin.last n) = u (Fin.last m)
        rw [snocR_last]

/-- A coordinate projection of an open nonempty set has nonempty interior. -/
theorem interior_image_projE_nonempty {p m : ℕ} (e : Fin p ↪ Fin m) {U : Set (Fin m → ℝ)}
    (hUo : IsOpen U) (hUne : U.Nonempty) :
    (interior ((fun u : Fin m → ℝ => u ∘ e) '' U)).Nonempty := by
  obtain ⟨u, hu⟩ := hUne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hUo u hu
  have hsub : Metric.ball (u ∘ e) r ⊆ (fun v : Fin m → ℝ => v ∘ e) '' U := by
    intro y hy
    have hy' : dist y (u ∘ e) < r := hy
    set w : Fin m → ℝ := fun j => if h : ∃ i, e i = j then y (Classical.choose h) else u j
    have hwe : w ∘ e = y := by
      funext i
      have hii : ∃ i', e i' = e i := ⟨i, rfl⟩
      simp only [w, Function.comp_apply, dif_pos hii]
      rw [e.injective (Classical.choose_spec hii)]
    have hwu : w ∈ Metric.ball u r := by
      rw [Metric.mem_ball, dist_pi_lt_iff hr]
      intro j
      by_cases hj : ∃ i, e i = j
      · simp only [w, dif_pos hj]
        have := (dist_pi_lt_iff hr).mp hy' (Classical.choose hj)
        rw [Function.comp_apply, Classical.choose_spec hj] at this
        exact this
      · simp only [w, dif_neg hj]
        simpa using hr
    exact ⟨w, hball hwu, hwe⟩
  have hne : (Metric.ball (u ∘ e) r).Nonempty :=
    ⟨u ∘ e, by rw [Metric.mem_ball, dist_self]; exact hr⟩
  exact hne.mono (interior_maximal hsub Metric.isOpen_ball)

/-- **Bridge lemma.** Every cell whose o-minimal dimension is at most `k` satisfies the
cell-dimension bound `k`. -/
theorem cellDimLE_of_isCell_dimLE {n k : ℕ} {C : Set (Fin n → ℝ)}
    (h : WilkiesDesign.IsCell n C) (hk : WilkiesDesign.DimLE C k) : CellDimLE n C k := by
  obtain ⟨m, e, Φ, hcell, hopen, hcont, hleft, hright⟩ := good_of_isCell h
  by_cases hle : m ≤ k
  · exact hcell.mono hle
  · push_neg at hle
    have hk1 : k + 1 ≤ m := hle
    have hUne : (ProjE e C).Nonempty := by
      obtain ⟨x, hx⟩ := isCell_nonempty h
      exact ⟨x ∘ e, x, hx, rfl⟩
    let e₂ : Fin (k + 1) ↪ Fin m := ⟨Fin.castLE hk1, Fin.castLE_injective hk1⟩
    have hne : (interior (ProjE (e₂.trans e) C)).Nonempty := by
      have h1 : ProjE (e₂.trans e) C = ProjE e₂ (ProjE e C) := by
        ext v
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x ∘ e, ⟨x, hx, rfl⟩, rfl⟩
        · rintro ⟨v', ⟨x, hx, rfl⟩, rfl⟩
          exact ⟨x, hx, rfl⟩
      rw [h1, ProjE]
      exact interior_image_projE_nonempty e₂ hopen hUne
    have hz := hk (e₂.trans e)
    change (interior ((fun x : Fin n → ℝ => x ∘ ⇑(e₂.trans e)) '' C)).Nonempty at hne
    rw [hz] at hne
    obtain ⟨y, hy⟩ := hne
    exact absurd hy (Set.notMem_empty y)

end Work.WilkiesH.Cell
