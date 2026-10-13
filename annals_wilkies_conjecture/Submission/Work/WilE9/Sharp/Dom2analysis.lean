import Mathlib
import Submission.Work.WilE9.Sharp.Main2
import Submission.Work.WilE9.Sharp.GlDerivContDiffAt2
import Submission.Work.WilE9.Sharp.hasFDerivAt_of_lineDeriv

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Work.WilE9.Sharp
open Classical Topology Filter
open WilkiesDesign WilkiesDesign.E

variable {n k : ℕ} {S : List (AEStratum n)} {f : (Fin n → ℝ) → ℝ}

/-! ## Extracting the component conditions of `contPart` and `diffPart` -/

lemma contPart_spec {G : Set (Fin (n+1) → ℝ)} {y : Fin n → ℝ} {t : ℝ}
    (h : Fin.snoc y t ∈ contPart G) :
    Fin.snoc y t ∈ G ∧ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y' : Fin n → ℝ,
      (∀ j : Fin n, |y' j - y j| < δ) → ∀ v' : ℝ, Fin.snoc y' v' ∈ G → |v' - t| < ε := by
  have h' := h
  simp only [contPart, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last] at h'
  exact h'

lemma diffPart_spec {G : Set (Fin (n+1) → ℝ)} {y : Fin n → ℝ} {t : ℝ} {i : Fin n}
    (h : Fin.snoc y t ∈ diffPart G i) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h' : ℝ, 0 < |h'| → |h'| < δ →
      ∀ y' : Fin n → ℝ, (∀ j : Fin n, y' j = y j + h' * (if j = i then 1 else 0)) →
      ∀ y₀ : ℝ, Fin.snoc y y₀ ∈ G → ∀ v' : ℝ, Fin.snoc y' v' ∈ G →
        |t - (v' - y₀) / h'| < ε := by
  have h' := h
  simp only [diffPart, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last] at h'
  exact h'

/-! ## Elementary points displaced in one coordinate -/

def shift (p : Fin n → ℝ) (i : Fin n) (t : ℝ) : Fin n → ℝ := p + t • Pi.single i (1:ℝ)

theorem shift_apply (p : Fin n → ℝ) (i : Fin n) (t : ℝ) (j : Fin n) :
    shift p i t j = p j + t * (if j = i then 1 else 0) := by
  simp [shift, Pi.single_apply]

theorem dist_shift (p : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    dist (shift p i t) p = |t| := by
  rw [shift, dist_eq_norm, add_sub_cancel_left, norm_smul, Pi.norm_single, Real.norm_eq_abs,
    norm_one, mul_one]

/-! ## The section of `Eset` -/

noncomputable def Esec (n : ℕ) (S : List (AEStratum n)) (L : List (Fin n))
    (y : Fin n → ℝ) : ℝ :=
  if h : ∃ t : ℝ, Fin.snoc y t ∈ Eset n S L then h.choose else 0

theorem Esec_mem {L : List (Fin n)} {y : Fin n → ℝ}
    (h : ∃ t : ℝ, Fin.snoc y t ∈ Eset n S L) : Fin.snoc y (Esec n S L y) ∈ Eset n S L := by
  rw [Esec, dif_pos h]
  exact h.choose_spec

theorem Eset_fibre_singleton {L : List (Fin n)}
    {U : Set (Fin n → ℝ)}
    (hU : U ⊆ WilkiesDesign.projLast (Eset n S L) ∩
        WilkiesDesign.projLast (contPart (Eset n S L)))
    {y : Fin n → ℝ} (hy : y ∈ U) {t₁ t₂ : ℝ}
    (h₁ : Fin.snoc y t₁ ∈ Eset n S L) (h₂ : Fin.snoc y t₂ ∈ Eset n S L) : t₁ = t₂ := by
  obtain ⟨-, t₀, ht₀⟩ := hU hy
  have hcont := (contPart_spec ht₀).2
  have key : ∀ t : ℝ, Fin.snoc y t ∈ Eset n S L → t = t₀ := by
    intro t ht
    have hconst : ∀ ε : ℝ, 0 < ε → |t - t₀| < ε := by
      intro ε hε
      obtain ⟨δ, hδ, hδ'⟩ := hcont ε hε
      exact hδ' y (fun j => by simp [hδ]) t ht
    refine sub_eq_zero.mp (abs_eq_zero.mp ?_)
    refine le_antisymm ?_ (abs_nonneg _)
    by_contra hlt
    have hpos : 0 < |t - t₀| := not_le.mp hlt
    have := hconst (|t - t₀| / 2) (by positivity)
    linarith
  exact (key t₁ h₁).trans (key t₂ h₂).symm

/-! ## The graph of a continuous function -/

theorem graphOf_contPart_of_continuousAt {z : Fin n → ℝ} (hf : ContinuousAt f z) :
    Fin.snoc z (f z) ∈ contPart (WilkiesDesign.graphOf f) := by
  rw [contPart]
  refine ⟨?_, ?_⟩
  · simp only [WilkiesDesign.graphOf, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last]
  · simp only [Fin.init_snoc, Fin.snoc_last]
    intro ε hε
    rw [Metric.continuousAt_iff] at hf
    obtain ⟨δ, hδ, hδ'⟩ := hf ε hε
    refine ⟨δ, hδ, fun x' hx' v' hv' => ?_⟩
    have hd : dist x' z < δ := (dist_pi_lt_iff hδ).mpr hx'
    have hv'e : v' = f x' := by
      simpa only [WilkiesDesign.graphOf, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last] using hv'
    rw [hv'e]
    simpa [Real.dist_eq] using hδ' hd

theorem continuousAt_of_mem_contPart_graphOf {y : Fin n → ℝ} {t : ℝ}
    (h : Fin.snoc y t ∈ contPart (WilkiesDesign.graphOf f)) : ContinuousAt f y := by
  obtain ⟨hmem, hcont⟩ := contPart_spec h
  have ht : t = f y := by
    simpa only [WilkiesDesign.graphOf, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last] using hmem
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := hcont ε hε
  refine ⟨δ, hδ, fun y' hy' => ?_⟩
  have hcomp : ∀ j : Fin n, |y' j - y j| < δ := (dist_pi_lt_iff hδ).mp hy'
  have hmem' : Fin.snoc y' (f y') ∈ WilkiesDesign.graphOf f := by
    simp only [WilkiesDesign.graphOf, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last]
  have := hδ' y' hcomp (f y') hmem'
  rw [ht] at this
  simpa [Real.dist_eq] using this

/-! ## The quotient form of a Fréchet derivative -/

theorem exists_quot_of_hasFDerivAt {g : (Fin n → ℝ) → ℝ} {z : Fin n → ℝ} (i : Fin n)
    (hg : HasFDerivAt g (fderiv ℝ g z) z) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < |t| → |t| < δ →
      |fderiv ℝ g z (Pi.single i 1) - (g (z + t • Pi.single i 1) - g z) / t| < ε := by
  have hb : ∀ᶠ y in 𝓝 z, ‖g y - g z - fderiv ℝ g z (y - z)‖ ≤ (ε/2) * ‖y - z‖ :=
    Asymptotics.isLittleO_iff.mp hg.isLittleO (by positivity)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp hb
  refine ⟨δ, hδ, fun t ht htd => ?_⟩
  have hmem : dist (z + t • Pi.single i (1:ℝ)) z < δ := by
    rw [show z + t • Pi.single i (1:ℝ) = shift z i t from rfl, dist_shift]; exact htd
  have hbnd := hδ' hmem
  have hbnd' : |g (z + t • Pi.single i (1:ℝ)) - g z - t * fderiv ℝ g z (Pi.single i (1:ℝ))|
      ≤ (ε/2) * |t| := by
    simpa only [Real.norm_eq_abs, add_sub_cancel_left, ContinuousLinearMap.map_smul,
      smul_eq_mul, norm_smul, Pi.norm_single, norm_one, mul_one] using hbnd
  have htne : t ≠ 0 := by rintro rfl; simp at ht
  have hkey : |g (z + t • Pi.single i (1:ℝ)) - g z - t * fderiv ℝ g z (Pi.single i (1:ℝ))|
      = |t| * |fderiv ℝ g z (Pi.single i (1:ℝ))
          - (g (z + t • Pi.single i (1:ℝ)) - g z) / t| := by
    rw [show g (z + t • Pi.single i (1:ℝ)) - g z - t * fderiv ℝ g z (Pi.single i (1:ℝ))
        = -(t * (fderiv ℝ g z (Pi.single i (1:ℝ))
            - (g (z + t • Pi.single i (1:ℝ)) - g z) / t)) from by
      field_simp
      ring,
      abs_neg, abs_mul]
  rw [hkey, mul_comm (ε/2)] at hbnd'
  have := le_of_mul_le_mul_left hbnd' ht
  linarith

/-! ## The domain characterisation -/

theorem DomSet_eq_analysis {n k : ℕ} {S : List (Work.WilE9.Sharp.AEStratum n)}
    {f : (Fin n → ℝ) → ℝ}
    (hsec : Work.WilE9.Sharp.SecSpec n k S f) (hlim : Work.WilE9.Sharp.LimSpec n k S f) :
    Work.WilE9.Sharp.DomSet n k S (WilkiesDesign.graphOf f) =
      {x : Fin n → ℝ | ContDiffAt ℝ k f x} := by
  apply Set.Subset.antisymm
  · -- ## `DomSet ⊆ {ContDiffAt ℝ k f}`
    intro x hx
    rw [DomSet, mem_interior_iff_mem_nhds] at hx
    obtain ⟨U, hUsub, hUo, hxU⟩ := mem_nhds_iff.mp hx
    -- the componentwise data of the big set at each point of `U`
    have hUraw : ∀ y ∈ U, ∀ (Ls : List (Fin n)), Ls.length ≤ k →
        y ∈ WilkiesDesign.projLast (Eset n S Ls) ∧
        y ∈ WilkiesDesign.projLast (contPart (Eset n S Ls)) ∧
        (Ls.length < k → ∀ i : Fin n,
          y ∈ WilkiesDesign.projLast (diffPart (Eset n S Ls) i ∩ Eset n S (i :: Ls))) := by
      intro y hy Ls hLs
      obtain ⟨⟨h2a, h2b⟩, h2c⟩ := Set.mem_iInter.mp (hUsub hy).2 ⟨Ls, hLs⟩
      refine ⟨h2a, h2b, fun hLlen i => ?_⟩
      rw [if_pos hLlen] at h2c
      exact Set.mem_iInter.mp h2c i
    have hfib : ∀ (Ls : List (Fin n)), Ls.length ≤ k → U ⊆
        WilkiesDesign.projLast (Eset n S Ls) ∩
        WilkiesDesign.projLast (contPart (Eset n S Ls)) :=
      fun Ls hLs y hy => ⟨(hUraw y hy Ls hLs).1, (hUraw y hy Ls hLs).2.1⟩
    have hsecU : ∀ (Ls : List (Fin n)) (hLs : Ls.length ≤ k) (y : Fin n → ℝ), y ∈ U →
        Fin.snoc y (Esec n S Ls y) ∈ Eset n S Ls :=
      fun Ls hLs y hy => Esec_mem (hUraw y hy Ls hLs).1
    have huniq : ∀ (Ls : List (Fin n)) (hLs : Ls.length ≤ k) (y : Fin n → ℝ), y ∈ U →
        ∀ t : ℝ, Fin.snoc y t ∈ Eset n S Ls → t = Esec n S Ls y :=
      fun Ls hLs y hy t ht =>
        Eset_fibre_singleton (hfib Ls hLs) hy ht (hsecU Ls hLs y hy)
    have hcontsec : ∀ (Ls : List (Fin n)) (hLs : Ls.length ≤ k) (y : Fin n → ℝ), y ∈ U →
        Fin.snoc y (Esec n S Ls y) ∈ contPart (Eset n S Ls) := by
      intro Ls hLs y hy
      obtain ⟨t, ht⟩ := (hUraw y hy Ls hLs).2.1
      have hte : t = Esec n S Ls y := huniq Ls hLs y hy t (contPart_spec ht).1
      rw [← hte]
      exact ht
    have hsec_cont : ∀ (Ls : List (Fin n)) (hLs : Ls.length ≤ k),
        ContinuousOn (Esec n S Ls) U := by
      intro Ls hLs
      rw [Metric.continuousOn_iff]
      intro y hy ε hε
      obtain ⟨δ, hδ, hδ'⟩ := (contPart_spec (hcontsec Ls hLs y hy)).2 ε hε
      refine ⟨δ, hδ, fun y' hy' hy'd => ?_⟩
      have hcomp : ∀ j : Fin n, |y' j - y j| < δ := (dist_pi_lt_iff hδ).mp hy'd
      have hres := hδ' y' hcomp (Esec n S Ls y') (hsecU Ls hLs y' hy')
      rwa [← Real.dist_eq] at hres
    -- the `Fréchet` derivative of the section, from the `diffPart` clause
    have hderiv1 : ∀ (Ls : List (Fin n)) (hLs : Ls.length < k) (y : Fin n → ℝ), y ∈ U →
        HasFDerivAt (Esec n S Ls)
          (∑ i : Fin n, (Esec n S (i :: Ls) y) •
            (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) y := by
      intro Ls hLs
      refine Work.WilE9.Sharp.hasFDerivAt_of_lineDeriv hUo (hsec_cont Ls (le_of_lt hLs))
        (fun i => Esec n S (i :: Ls)) (fun i => hsec_cont (i :: Ls) ?_) ?_
      · simp only [List.length_cons]; omega
      · intro i p hp ε hε
        obtain ⟨δ₀, hδ₀, hδ₀'⟩ := Metric.mem_nhds_iff.mp (hUo.mem_nhds hp)
        have htk : (i :: Ls).length ≤ k := by simp only [List.length_cons]; omega
        obtain ⟨t₀, ht₀⟩ := (hUraw p hp Ls (le_of_lt hLs)).2.2 hLs i
        have ht₀' : t₀ = Esec n S (i :: Ls) p :=
          Eset_fibre_singleton (hfib (i :: Ls) htk) hp ht₀.2 (hsecU (i :: Ls) htk p hp)
        obtain ⟨δ₁, hδ₁, hδ₁'⟩ := diffPart_spec ht₀.1 ε hε
        refine ⟨min δ₁ δ₀, lt_min hδ₁ hδ₀, fun t ht htd => ?_⟩
        have ht₁ : |t| < δ₁ := lt_of_lt_of_le htd (min_le_left _ _)
        have ht₀'' : |t| < δ₀ := lt_of_lt_of_le htd (min_le_right _ _)
        have hmem : shift p i t ∈ U := by
          apply hδ₀'; rw [Metric.mem_ball, dist_shift]; exact ht₀''
        have hres := hδ₁' t ht ht₁ (shift p i t) (shift_apply p i t) (Esec n S Ls p)
          (hsecU Ls (le_of_lt hLs) p hp) (Esec n S Ls (shift p i t))
          (hsecU Ls (le_of_lt hLs) (shift p i t) hmem)
        rw [ht₀'] at hres
        have htne : t ≠ 0 := by rintro rfl; simp at ht
        change |Esec n S Ls (shift p i t) - Esec n S Ls p - t * Esec n S (i :: Ls) p| ≤ ε * |t|
        have hkey : |Esec n S Ls (shift p i t) - Esec n S Ls p - t * Esec n S (i :: Ls) p|
            = |t| * |Esec n S (i :: Ls) p
                - (Esec n S Ls (shift p i t) - Esec n S Ls p) / t| := by
          rw [show Esec n S Ls (shift p i t) - Esec n S Ls p - t * Esec n S (i :: Ls) p
              = -(t * (Esec n S (i :: Ls) p
                  - (Esec n S Ls (shift p i t) - Esec n S Ls p) / t)) from by
            field_simp
            ring,
            abs_neg, abs_mul]
        rw [hkey]
        calc |t| * |Esec n S (i :: Ls) p
                - (Esec n S Ls (shift p i t) - Esec n S Ls p) / t|
            ≤ |t| * ε := le_of_lt (mul_lt_mul_of_pos_left hres ht)
          _ = ε * |t| := by ring
    -- the section agrees with `glDeriv`
    have hsec_gl : ∀ Ls : List (Fin n), Ls.length ≤ k →
        ∀ y ∈ U, Esec n S Ls y = Work.WilE9.glDeriv Ls f y := by
      intro Ls
      induction Ls with
      | nil =>
        intro _ y hy
        -- `Esec n S [] y = f y`
        have hcl : y ∈ closure {z : Fin n → ℝ | ContDiffAt ℝ ([] : List (Fin n)).length f z} :=
          hlim [] (by simp) y ⟨Esec n S [] y, hsecU [] (by simp) y hy⟩
        set T : Set (Fin n → ℝ) := {z | ContDiffAt ℝ ([] : List (Fin n)).length f z} with hT
        have hclU : y ∈ closure (T ∩ U) := by
          rw [Metric.mem_closure_iff] at hcl ⊢
          intro ε hε
          obtain ⟨ρ, hρ, hρU⟩ := Metric.mem_nhds_iff.mp (hUo.mem_nhds hy)
          obtain ⟨b, hbT, hbd⟩ := hcl (min ε ρ) (by positivity)
          have hb_ball : b ∈ Metric.ball y ρ := by
            rw [Metric.mem_ball, dist_comm]
            exact lt_of_lt_of_le hbd (min_le_right _ _)
          exact ⟨b, ⟨hbT, hρU hb_ball⟩, lt_of_lt_of_le hbd (min_le_left _ _)⟩
        have hfcont : ContinuousAt f y := by
          obtain ⟨t, ht⟩ := (hUsub hy).1
          exact continuousAt_of_mem_contPart_graphOf ht
        have hEsc : ContinuousAt (Esec n S ([] : List (Fin n))) y :=
          (hsec_cont [] (by simp)).continuousAt (hUo.mem_nhds hy)
        have hzero : ∀ z ∈ T ∩ U, Esec n S [] z - f z = 0 := by
          rintro z ⟨hzT, hzU⟩
          have hzT' : ContDiffAt ℝ ([] : List (Fin n)).length f z := by
            have h := hzT
            rw [hT] at h
            simpa only [Set.mem_ofPred_eq, List.length_nil] using h
          have hzE : Fin.snoc z (f z) ∈ Eset n S ([] : List (Fin n)) :=
            (hsec [] (by simp) z (f z) hzT').mpr rfl
          have huniq' : f z = Esec n S [] z := huniq [] (by simp) z hzU (f z) hzE
          rw [huniq']; ring
        have hne : NeBot (𝓝[T ∩ U] y) := mem_closure_iff_nhdsWithin_neBot.mp hclU
        have h1 : Tendsto (fun z => Esec n S ([] : List (Fin n)) z - f z) (𝓝[T ∩ U] y)
            (𝓝 (Esec n S [] y - f y)) :=
          (hEsc.sub hfcont).tendsto.mono_left nhdsWithin_le_nhds
        have h2 : Tendsto (fun z => Esec n S ([] : List (Fin n)) z - f z) (𝓝[T ∩ U] y)
            (𝓝 0) := by
          refine tendsto_const_nhds.congr' ?_
          rw [Filter.eventuallyEq_iff_exists_mem]
          exact ⟨T ∩ U, self_mem_nhdsWithin, fun z hz => (hzero z hz).symm⟩
        exact sub_eq_zero.mp (tendsto_nhds_unique h1 h2)
      | cons i L' ih =>
        intro hlen y hy
        have hL'l : L'.length < k := by simp only [List.length_cons] at hlen; omega
        have hL'k : L'.length ≤ k := le_of_lt hL'l
        have hIH : ∀ y ∈ U, Esec n S L' y = Work.WilE9.glDeriv L' f y := ih hL'k
        have hfd := hderiv1 L' hL'l y hy
        have hev : Esec n S L' =ᶠ[𝓝 y] Work.WilE9.glDeriv L' f :=
          Filter.eventuallyEq_iff_exists_mem.mpr ⟨U, hUo.mem_nhds hy, hIH⟩
        have hfdr : fderiv ℝ (Work.WilE9.glDeriv L' f) y
            = ∑ l : Fin n, (Esec n S (l :: L') y) •
              (ContinuousLinearMap.proj l : (Fin n → ℝ) →L[ℝ] ℝ) := by
          rw [← hev.fderiv_eq, hfd.fderiv]
        rw [show Work.WilE9.glDeriv (i :: L') f y
              = fderiv ℝ (Work.WilE9.glDeriv L' f) y (Pi.single i 1) from rfl, hfdr]
        rw [ContinuousLinearMap.sum_apply, Finset.sum_eq_single i]
        · rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, Pi.single_eq_same]
          simp
        · intro l _ hl
          rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
            Pi.single_eq_of_ne hl]
          simp
        · intro hi; exact absurd (Finset.mem_univ i) hi
    -- downward induction on the order: the section is `C^{k-|L|}`
    have hCD : ∀ j, j ≤ k → ∀ Ls : List (Fin n), Ls.length = k - j →
        ContDiffOn ℝ j (Esec n S Ls) U := by
      intro j
      induction j with
      | zero =>
        intro _ Ls hLs
        have hlen : Ls.length ≤ k := by omega
        simpa using hsec_cont Ls hlen
      | succ j ih =>
        intro hj Ls hLs
        have hjk : j ≤ k := by omega
        have hlen : Ls.length ≤ k := by omega
        have hlt : Ls.length < k := by omega
        have hder := hderiv1 Ls hlt
        have hfdr : ∀ y ∈ U, fderiv ℝ (Esec n S Ls) y
            = ∑ i : Fin n, (Esec n S (i :: Ls) y) •
              (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ) :=
          fun y hy => (hder y hy).fderiv
        have hsumCD : ContDiffOn ℝ j
            (fun y => ∑ i : Fin n, (Esec n S (i :: Ls) y) •
              (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) U := by
          refine ContDiffOn.sum (fun i _ => ?_)
          have hik : (i :: Ls).length = k - j := by simp only [List.length_cons]; omega
          exact (ih hjk (i :: Ls) hik).smul_const _
        have hcd : ContDiffOn ℝ j (fderiv ℝ (Esec n S Ls)) U :=
          hsumCD.congr (fun y hy => hfdr y hy)
        rw [show (↑(j + 1) : WithTop ℕ∞) = (j : WithTop ℕ∞) + 1 from by push_cast; ring]
        rw [contDiffOn_succ_iff_fderiv_of_isOpen hUo]
        exact ⟨fun y hy => (hder y hy).differentiableAt.differentiableWithinAt,
          fun h => absurd h (by simp), hcd⟩
    -- conclude
    have hfCD : ContDiffOn ℝ k f U := by
      have h0 : ContDiffOn ℝ k (Esec n S ([] : List (Fin n))) U := hCD k le_rfl [] (by simp)
      exact h0.congr (fun y hy => (hsec_gl [] (by simp) y hy).symm)
    simpa only [Set.mem_ofPred_eq] using hfCD.contDiffAt (hUo.mem_nhds hxU)
  · -- ## `{ContDiffAt ℝ k f} ⊆ DomSet`
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    rw [DomSet, mem_interior_iff_mem_nhds]
    obtain ⟨u, hu, hcdu⟩ := hx.contDiffOn le_rfl (by simp)
    obtain ⟨r, hr, hru⟩ := Metric.mem_nhds_iff.mp hu
    refine Metric.mem_nhds_iff.mpr ⟨r, hr, fun z hz => ?_⟩
    have hcdOn : ∀ y ∈ Metric.ball x r, ContDiffAt ℝ k f y := fun y hy =>
      hcdu.contDiffAt (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hy) hru)
    have hzcd : ContDiffAt ℝ k f z := hcdOn z hz
    have hglcont : ∀ (Ls : List (Fin n)) (hLs : Ls.length ≤ k), ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ z' : Fin n → ℝ, dist z' z < δ →
          dist (Work.WilE9.glDeriv Ls f z') (Work.WilE9.glDeriv Ls f z) < ε :=
      fun Ls hLs => (Metric.continuousAt_iff.mp (GlDerivContDiffAt2 hzcd hLs).continuousAt)
    have hderiv : ∀ Ls : List (Fin n), Ls.length < k →
        HasFDerivAt (Work.WilE9.glDeriv Ls f) (fderiv ℝ (Work.WilE9.glDeriv Ls f) z) z := by
      intro Ls hLs
      have hne : ((k - Ls.length : ℕ) : WithTop ℕ∞) ≠ 0 := by
        rw [Nat.cast_ne_zero]
        omega
      exact ((GlDerivContDiffAt2 hzcd (le_of_lt hLs)).differentiableAt hne).hasFDerivAt
    refine ⟨⟨f z, graphOf_contPart_of_continuousAt hzcd.continuousAt⟩, ?_⟩
    refine Set.mem_iInter.mpr (fun L => ?_)
    have hLlen : L.1.length ≤ k := L.2
    have hzL : ContDiffAt ℝ L.1.length f z := hzcd.of_le (by exact_mod_cast hLlen)
    refine ⟨⟨⟨Work.WilE9.glDeriv L.1 f z, (hsec L.1 hLlen z _ hzL).mpr rfl⟩, ?_⟩, ?_⟩
    · -- `projLast (contPart (Eset n S L.1))`
      refine ⟨Work.WilE9.glDeriv L.1 f z, ?_⟩
      simp only [contPart, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last]
      refine ⟨(hsec L.1 hLlen z _ hzL).mpr rfl, ?_⟩
      intro ε hε
      obtain ⟨δ₁, hδ₁, hδ₁'⟩ := hglcont L.1 hLlen ε hε
      obtain ⟨δ₀, hδ₀, hδ₀'⟩ := Metric.mem_nhds_iff.mp (Metric.isOpen_ball.mem_nhds hz)
      refine ⟨min δ₁ δ₀, lt_min hδ₁ hδ₀, fun z' hz' v' hv' => ?_⟩
      have hz'd : dist z' z < min δ₁ δ₀ := (dist_pi_lt_iff (lt_min hδ₁ hδ₀)).mpr hz'
      have hz'B : z' ∈ Metric.ball x r :=
        hδ₀' (lt_of_lt_of_le hz'd (min_le_right _ _))
      have hv'' : v' = Work.WilE9.glDeriv L.1 f z' :=
        (hsec L.1 hLlen z' v' ((hcdOn z' hz'B).of_le (by exact_mod_cast hLlen))).mp hv'
      rw [hv'']
      exact hδ₁' z' (lt_of_lt_of_le hz'd (min_le_left _ _))
    · by_cases hcase : L.1.length < k
      · rw [if_pos hcase]
        refine Set.mem_iInter.mpr (fun i => ?_)
        refine ⟨Work.WilE9.glDeriv (i :: L.1) f z, ?_, ?_⟩
        · -- `diffPart (Eset n S L.1) i`
          simp only [diffPart, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last]
          intro ε hε
          obtain ⟨δ₁, hδ₁, hδ₁'⟩ := exists_quot_of_hasFDerivAt i (hderiv L.1 hcase) hε
          obtain ⟨δ₀, hδ₀, hδ₀'⟩ := Metric.mem_nhds_iff.mp (Metric.isOpen_ball.mem_nhds hz)
          refine ⟨min δ₁ δ₀, lt_min hδ₁ hδ₀, fun h hh hhd x' hx' y₀ hy₀ v' hv' => ?_⟩
          have hh₁ : |h| < δ₁ := lt_of_lt_of_le hhd (min_le_left _ _)
          have hh₀ : |h| < δ₀ := lt_of_lt_of_le hhd (min_le_right _ _)
          have hxe : x' = shift z i h := by
            funext j; rw [hx' j, shift_apply]
          have hx'B : x' ∈ Metric.ball x r := by
            apply hδ₀'; rw [Metric.mem_ball, hxe, dist_shift]; exact hh₀
          have hxm : ContDiffAt ℝ L.1.length f x' :=
            (hcdOn x' hx'B).of_le (by exact_mod_cast hLlen)
          have hy₀' : y₀ = Work.WilE9.glDeriv L.1 f z := (hsec L.1 hLlen z y₀ hzL).mp hy₀
          have hv'' : v' = Work.WilE9.glDeriv L.1 f x' := (hsec L.1 hLlen x' v' hxm).mp hv'
          rw [hy₀', hv'', hxe]
          exact hδ₁' h hh hh₁
        · -- `Eset n S (i :: L.1)`
          have hik : (i :: L.1).length ≤ k := by simp only [List.length_cons]; omega
          exact (hsec (i :: L.1) hik z _ (hzcd.of_le (by exact_mod_cast hik))).mpr rfl
      · rw [if_neg hcase]
        exact Set.mem_univ z


end Work.WilE9.Sharp
