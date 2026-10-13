import Mathlib
import Submission.Work.WilkiesH.Strat.CellBand
import Submission.Work.WilkiesH.Cell.cellDimLE_of_isCell_dimLE

namespace Work.WilkiesH.Strat

open Work.WilkiesH.Cell

/-- **Band chart for a `CellBand`-cell.**

The construction is the same as that of `Work.WilkiesH.Cell.good_of_isCell`
(which handles the `IsCell` predicate together with the dimension bookkeeping),
but it is carried out directly by recursion on the band count `d`: the `graph`
step keeps the index `d`, and the `band` step increases it by one.  The output
is a coordinate embedding `e : Fin d ↪ Fin n` together with a continuous section
`Φ` of the projection `ProjE e κ`, which is a genuine two-sided inverse on `κ`. -/
theorem bandChart_of_cellBand {n d : ℕ} {κ : Set (Fin n → ℝ)}
    (h : Work.WilkiesH.Strat.CellBand n κ d) :
    ∃ (e : Fin d ↪ Fin n) (Φ : (Fin d → ℝ) → (Fin n → ℝ)),
      IsOpen (Work.WilkiesH.Cell.ProjE e κ) ∧
      ContinuousOn Φ (Work.WilkiesH.Cell.ProjE e κ) ∧
      (∀ x ∈ κ, Φ (x ∘ e) = x) ∧
      (∀ u ∈ Work.WilkiesH.Cell.ProjE e κ, Φ u ∘ e = u) := by
  refine CellBand.rec (motive := fun n κ d _ =>
      ∃ (e : Fin d ↪ Fin n) (Φ : (Fin d → ℝ) → (Fin n → ℝ)),
        IsOpen (ProjE e κ) ∧
        ContinuousOn Φ (ProjE e κ) ∧
        (∀ x ∈ κ, Φ (x ∘ e) = x) ∧
        (∀ u ∈ ProjE e κ, Φ u ∘ e = u)) ?_ ?_ ?_ h
  · -- zero
    refine ⟨(Equiv.refl (Fin 0)).toEmbedding, id, ?_, ?_, ?_, ?_⟩
    · have hh : ProjE (Equiv.refl (Fin 0)).toEmbedding (Set.univ : Set (Fin 0 → ℝ))
          = Set.univ := by
        rw [ProjE, Set.image_univ, Set.range_eq_univ]
        exact fun y => ⟨y, Subsingleton.elim _ _⟩
      rw [hh]; exact isOpen_univ
    · exact continuous_id.continuousOn
    · intro x _
      exact Subsingleton.elim _ _
    · intro u _
      exact Subsingleton.elim _ _
  · -- graph
    intro n C d hC f hf ih
    obtain ⟨e₀, Φ₀, hopen, hcont, hleft, hright⟩ := ih
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
    refine ⟨e₀.trans succEmb, (fun u => snocR (Φ₀ u) (f (Φ₀ u))), ?_, ?_, ?_, ?_⟩
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
    intro n C d hC a b ha hb hab ih
    obtain ⟨e₀, Φ₀, hopen, hcont, hleft, hright⟩ := ih
    have hΦmaps : Set.MapsTo Φ₀ (ProjE e₀ C) C := fun u hu => by
      obtain ⟨x, hx, hxu⟩ := hu
      rw [← hxu, hleft x hx]; exact hx
    have hinit : Continuous (Fin.init : (Fin (d + 1) → ℝ) → (Fin d → ℝ)) :=
      continuous_pi fun i => continuous_apply _
    have hset : ProjE (bandEmb e₀)
        {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧ a (Fin.init z) < ↑(z (Fin.last n)) ∧
          ↑(z (Fin.last n)) < b (Fin.init z)}
        = {w : Fin (d + 1) → ℝ | Fin.init w ∈ ProjE e₀ C ∧
            a (Φ₀ (Fin.init w)) < ↑(w (Fin.last d)) ∧
            ↑(w (Fin.last d)) < b (Φ₀ (Fin.init w))} := by
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
        refine ⟨snocR y (w (Fin.last d)), ⟨?_, ?_, ?_⟩, ?_⟩
        · rw [init_snocR]; exact hy
        · rw [init_snocR, snocR_last, ← hyw]; exact h1
        · rw [init_snocR, snocR_last, ← hyw]; exact h2
        · dsimp only
          rw [comp_bandEmb, init_snocR, snocR_last, hyu']
          exact snocR_init_self w
    refine ⟨bandEmb e₀, (fun u => snocR (Φ₀ (Fin.init u)) (u (Fin.last d))),
      ?_, ?_, ?_, ?_⟩
    · rw [hset]
      set U := ProjE e₀ C with hUdef
      set F : (Fin (d + 1) → ℝ) → EReal := fun w => a (Φ₀ (Fin.init w))
      set F' : (Fin (d + 1) → ℝ) → EReal := fun w => b (Φ₀ (Fin.init w))
      set G : (Fin (d + 1) → ℝ) → EReal := fun w => ↑(w (Fin.last d))
      have hV : IsOpen {w : Fin (d + 1) → ℝ | Fin.init w ∈ U} := hopen.preimage hinit
      have hFcont : ContinuousOn F {w : Fin (d + 1) → ℝ | Fin.init w ∈ U} :=
        (ha.comp hcont hΦmaps).comp hinit.continuousOn (fun w hw => hw)
      have hF'cont : ContinuousOn F' {w : Fin (d + 1) → ℝ | Fin.init w ∈ U} :=
        (hb.comp hcont hΦmaps).comp hinit.continuousOn (fun w hw => hw)
      have hGcont : ContinuousOn G {w : Fin (d + 1) → ℝ | Fin.init w ∈ U} :=
        (continuous_coe_real_ereal.comp (continuous_apply (Fin.last d))).continuousOn
      have hlt : IsOpen {p : EReal × EReal | p.1 < p.2} :=
        isOpen_lt continuous_fst continuous_snd
      have h1 : IsOpen ({w : Fin (d + 1) → ℝ | Fin.init w ∈ U} ∩
          (fun w => (F w, G w)) ⁻¹' {p : EReal × EReal | p.1 < p.2}) :=
        ContinuousOn.isOpen_inter_preimage (hFcont.prodMk hGcont) hV hlt
      have h2 : IsOpen ({w : Fin (d + 1) → ℝ | Fin.init w ∈ U} ∩
          (fun w => (G w, F' w)) ⁻¹' {p : EReal × EReal | p.1 < p.2}) :=
        ContinuousOn.isOpen_inter_preimage (hGcont.prodMk hF'cont) hV hlt
      have hfinal : {w : Fin (d + 1) → ℝ | Fin.init w ∈ U ∧ F w < G w ∧ G w < F' w}
          = ({w : Fin (d + 1) → ℝ | Fin.init w ∈ U} ∩
              (fun w => (F w, G w)) ⁻¹' {p : EReal × EReal | p.1 < p.2}) ∩
            ({w : Fin (d + 1) → ℝ | Fin.init w ∈ U} ∩
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
      · exact ((continuous_apply (Fin.last d)).continuousOn).congr
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
        show snocR (Φ₀ (Fin.init u)) (u (Fin.last d)) (Fin.castSucc (e₀ i'))
            = u (Fin.castSucc i')
        rw [snocR_castSucc]
        exact congrFun (hright (Fin.init u) hinit_u) i'
      · rw [Function.comp_apply, bandEmb_last]
        show snocR (Φ₀ (Fin.init u)) (u (Fin.last d)) (Fin.last n) = u (Fin.last d)
        rw [snocR_last]

end Work.WilkiesH.Strat
