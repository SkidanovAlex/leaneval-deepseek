import Mathlib
import Submission.Work.Drive.localConstancy_surface

/-!
# Finiteness of the meet set of two periodic curves, from regularity

`Work.Drive.meetS L D` is the set of parameter pairs `(t, v)` in the fundamental square
`[0,1) × [0,1)` with `L t = D v`, where `L` and `D` are `1`-periodic.  This file proves that it is
**finite** as soon as

* every meet point is *interior* in the parameter square (`hint`), and
* every meet point is *regular* (`hreg`): `fderiv ℝ (L · − D ·)` is surjective there — with
  `finrank ℝ (ℝ × ℝ) = finrank ℝ E` (`hdim`) this is the transversality of the two curves at a meet
  point.

The argument uses no Sard:

* if `S = meetS L D` were infinite, then, `S ⊆ [0,1]²` with the square compact, some sequence of
  distinct points of `S` would converge to a point `a ∈ [0,1]²`;
* if `a` is *interior*, then `a ∈ S`, and `hreg` (surjective derivative between spaces of equal
  finite dimension) plus the implicit function theorem
  (`Work.Drive.exists_local_solution_of_surjective`) makes `a` an isolated zero of
  `F = L · − D ·`, contradicting the convergence of a sequence of distinct zeros;
* if instead `a` sits on the boundary of the square, say `a.1 ∈ {0,1}`, then the periodicity
  `L 1 = L 0` produces a point of `S` with a *zero* coordinate — which `hint` forbids.  (This is the
  same use of periodicity as in `Work.Drive.eventually_meetS_cover`: the seam is where the loop closes
  up, and interiority is exactly what rules out meets living there.)

So `meetS` is finite, which removes the `hfin` hypothesis of the local constancy engine
`Work.Drive.eventually_ncard_meetS_eq`.
-/

namespace Work.Drive

open Filter
open scoped Topology ContDiff

noncomputable section

theorem meetS_finite_of_regular {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (L D : ℝ → E) (hL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) L)
    (hLper : ∀ t : ℝ, L (t + 1) = L t)
    (hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) D)
    (hDper : ∀ v : ℝ, D (v + 1) = D v)
    (hdim : Module.finrank ℝ (ℝ × ℝ) = Module.finrank ℝ E)
    (hint : ∀ p ∈ Work.Drive.meetS L D, p.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ p.2 ∈ Set.Ioo (0 : ℝ) 1)
    (hreg : ∀ p ∈ Work.Drive.meetS L D,
      Function.Surjective (fderiv ℝ (fun q : ℝ × ℝ => L q.1 - D q.2) p)) :
    (Work.Drive.meetS L D).Finite := by
  classical
  by_contra hfin
  have hInf : (meetS L D).Infinite := hfin
  have hcont : Continuous (fun q : ℝ × ℝ => L q.1 - D q.2) := by
    have h1 : Continuous L := hL.continuous
    have h2 : Continuous D := hD.continuous
    fun_prop
  let emb : ℕ ↪ (meetS L D) := Set.Infinite.natEmbedding (meetS L D) hInf
  set p : ℕ → ℝ × ℝ := fun n => (emb n : ℝ × ℝ) with hpdef
  have hp_mem : ∀ n, p n ∈ meetS L D := fun n => (emb n).2
  have hp_inj : Function.Injective p := by
    intro m n h
    exact Function.Embedding.injective emb (Subtype.ext h)
  have hpm : ∀ n, p n ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
    intro n
    obtain ⟨ht, hv, -⟩ := mem_meetS.mp (hp_mem n)
    exact ⟨⟨ht.1, le_of_lt ht.2⟩, ⟨hv.1, le_of_lt hv.2⟩⟩
  obtain ⟨a, ha, φ, hφ, hpt⟩ := (isCompact_Icc.prod isCompact_Icc).tendsto_subseq hpm
  have ha1 : 0 ≤ a.1 ∧ a.1 ≤ 1 := ha.1
  have ha2 : 0 ≤ a.2 ∧ a.2 ≤ 1 := ha.2
  -- the limit point is a zero of the difference map
  have hF0 : L a.1 - D a.2 = 0 := by
    have h1 : Tendsto (fun n : ℕ => L (p (φ n)).1 - D (p (φ n)).2) atTop
        (nhds (L a.1 - D a.2)) :=
      (hcont.continuousAt (x := a)).tendsto.comp hpt
    have h2 : Tendsto (fun n : ℕ => L (p (φ n)).1 - D (p (φ n)).2) atTop (nhds 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards with n
      exact (sub_eq_zero.mpr (mem_meetS.mp (hp_mem (φ n))).2.2).symm
    exact tendsto_nhds_unique h1 h2
  have hLa : L a.1 = D a.2 := sub_eq_zero.mp hF0
  have hzero : ∀ n, L (p n).1 - D (p n).2 = 0 :=
    fun n => sub_eq_zero.mpr (mem_meetS.mp (hp_mem n)).2.2
  -- interior limit points are isolated zeros
  have hInt : a.1 ∈ Set.Ioo (0 : ℝ) 1 → a.2 ∈ Set.Ioo (0 : ℝ) 1 → False := by
    intro ha1' ha2'
    have hamem : a ∈ meetS L D :=
      ⟨⟨le_of_lt ha1'.1, ha1'.2⟩, ⟨le_of_lt ha2'.1, ha2'.2⟩, hLa⟩
    obtain ⟨ε, δ, ψ, hε, hδ, hψ0, -, -, huniq⟩ :=
      exists_local_solution_of_surjective (F := ℝ × ℝ) (E := E)
        (fun (_ : ℝ) (q : ℝ × ℝ) => L q.1 - D q.2) (by fun_prop) hdim
        (sub_eq_zero.mpr hLa) (hreg a hamem)
    have hev : ∀ᶠ n in atTop, ‖p (φ n) - a‖ < δ := by
      filter_upwards [hpt.eventually (Metric.ball_mem_nhds a hδ)] with n hn
      simpa [Metric.mem_ball, dist_eq_norm] using hn
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
    have h1 : p (φ N) = a :=
      (huniq 0 (by rw [abs_zero]; exact hε) (p (φ N)) (hN N le_rfl) (hzero (φ N))).trans hψ0
    have h2 : p (φ (N + 1)) = a :=
      (huniq 0 (by rw [abs_zero]; exact hε) (p (φ (N + 1))) (hN (N + 1) (Nat.le_succ N))
        (hzero (φ (N + 1)))).trans hψ0
    have heq : p (φ N) = p (φ (N + 1)) := by rw [h1, h2]
    have hφeq : φ N = φ (N + 1) := hp_inj heq
    have hlt : φ N < φ (N + 1) := hφ (Nat.lt_succ_self N)
    omega
  -- a limit point on the left/right seam produces a meet point with a zero coordinate
  have hB1 : a.1 = 0 ∨ a.1 = 1 → False := by
    intro h
    have hL0 : L 0 = L a.1 := by
      rcases h with h | h
      · rw [h]
      · rw [h]; simpa using (hLper 0).symm
    have hL0D : L 0 = D a.2 := by rw [hL0, hLa]
    rcases lt_or_eq_of_le ha2.2 with hlt | heq
    · have hmem : ((0 : ℝ), a.2) ∈ meetS L D :=
        ⟨⟨le_refl 0, zero_lt_one⟩, ⟨ha2.1, hlt⟩, hL0D⟩
      have hc : (0 : ℝ) < 0 := (hint ((0 : ℝ), a.2) hmem).1.1
      exact absurd hc (lt_irrefl 0)
    · have hD0 : D 0 = D a.2 := by
        rw [heq]; simpa using (hDper 0).symm
      have hmem : ((0 : ℝ), (0 : ℝ)) ∈ meetS L D :=
        ⟨⟨le_refl 0, zero_lt_one⟩, ⟨le_refl 0, zero_lt_one⟩, by rw [hL0D, hD0]⟩
      have hc : (0 : ℝ) < 0 := (hint ((0 : ℝ), (0 : ℝ)) hmem).1.1
      exact absurd hc (lt_irrefl 0)
  -- a limit point on the bottom/top seam produces a meet point with a zero coordinate
  have hB2 : a.2 = 0 ∨ a.2 = 1 → False := by
    intro h
    have hD0 : D 0 = D a.2 := by
      rcases h with h | h
      · rw [h]
      · rw [h]; simpa using (hDper 0).symm
    have hLD0 : L a.1 = D 0 := by rw [hLa, hD0]
    rcases lt_or_eq_of_le ha1.2 with hlt | heq
    · have hmem : (a.1, (0 : ℝ)) ∈ meetS L D :=
        ⟨⟨ha1.1, hlt⟩, ⟨le_refl 0, zero_lt_one⟩, hLD0⟩
      have hc : (0 : ℝ) < 0 := (hint (a.1, (0 : ℝ)) hmem).2.1
      exact absurd hc (lt_irrefl 0)
    · have hL0 : L 0 = L a.1 := by
        rw [heq]; simpa using (hLper 0).symm
      have hmem : ((0 : ℝ), (0 : ℝ)) ∈ meetS L D :=
        ⟨⟨le_refl 0, zero_lt_one⟩, ⟨le_refl 0, zero_lt_one⟩, by rw [hL0, hLD0]⟩
      have hc : (0 : ℝ) < 0 := (hint ((0 : ℝ), (0 : ℝ)) hmem).2.1
      exact absurd hc (lt_irrefl 0)
  have hcase1 : a.1 ∈ Set.Ioo (0 : ℝ) 1 ∨ a.1 = 0 ∨ a.1 = 1 := by
    rcases lt_or_ge (0 : ℝ) a.1 with h | h
    · rcases lt_or_ge a.1 1 with h2 | h2
      · exact Or.inl ⟨h, h2⟩
      · exact Or.inr (Or.inr (le_antisymm ha1.2 h2))
    · exact Or.inr (Or.inl (le_antisymm h ha1.1))
  have hcase2 : a.2 ∈ Set.Ioo (0 : ℝ) 1 ∨ a.2 = 0 ∨ a.2 = 1 := by
    rcases lt_or_ge (0 : ℝ) a.2 with h | h
    · rcases lt_or_ge a.2 1 with h2 | h2
      · exact Or.inl ⟨h, h2⟩
      · exact Or.inr (Or.inr (le_antisymm ha2.2 h2))
    · exact Or.inr (Or.inl (le_antisymm h ha2.1))
  rcases hcase1 with h1 | h1 | h1
  · rcases hcase2 with h2 | h2 | h2
    · exact hInt h1 h2
    · exact hB2 (Or.inl h2)
    · exact hB2 (Or.inr h2)
  · exact hB1 (Or.inl h1)
  · exact hB1 (Or.inr h1)

end

end Work.Drive
