import Mathlib

open Filter Topology
open scoped Topology

namespace Work.WilE4.CAD

/-- **Lifting a limit through locally bounded fibres, relative version.** If `A ⊆ D ∩ S` with `D`
and `S` closed, the `A`-fibres are bounded by `B` on a neighbourhood of `x`, and `x` is a limit
point of the projection `Prod.fst '' A`, then there is a point of `D ∩ S` above `x`.

Proof sketch. Choose an open neighbourhood `U` of `x` on which every `A`-fibre is bounded by `B`,
and a sequence `v n → x` of first coordinates of points `(v n, t n) ∈ A`. Eventually `v n ∈ U`, so
the `t n` are bounded by `B`; Bolzano–Weierstrass yields a convergent subsequence `t (φ n) → a`,
and then `(v (φ n), t (φ n)) → (x, a)` is a sequence in `A` (hence in `D` and in `S`), so closedness
of `D` and `S` forces `(x, a) ∈ D ∩ S`. -/
lemma exists_snd_of_mem_closure_fst_rel {k : ℕ} {A D S : Set ((Fin k → ℝ) × ℝ)}
    (hD : IsClosed D) (hS : IsClosed S) (hAD : A ⊆ D) (hAS : A ⊆ S)
    {x : Fin k → ℝ} {B : ℝ}
    (hbdd : ∀ᶠ x' in nhds x, ∀ t : ℝ, (x', t) ∈ A → |t| ≤ B)
    (hx : x ∈ closure (Prod.fst '' A)) : ∃ t : ℝ, (x, t) ∈ D ∩ S := by
  classical
  -- An open neighbourhood `U` of `x` on which the `A`-fibres are bounded by `B`.
  obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp hbdd
  -- A sequence of first coordinates of points of `A`, converging to `x`.
  obtain ⟨v, hvA, hvx⟩ := mem_closure_iff_seq_limit.mp hx
  -- Lift it to actual points `(v n, t n) ∈ A`.
  have hcho : ∀ n, ∃ t : ℝ, (v n, t) ∈ A := by
    intro n
    obtain ⟨p, hpA, hp⟩ := (Set.mem_image Prod.fst A (v n)).mp (hvA n)
    exact ⟨p.2, by rwa [← hp]⟩
  choose t ht using hcho
  -- Eventually the first coordinates lie in `U`, hence the second coordinates are bounded by `B`.
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hvx.eventually (hUopen.mem_nhds hxU))
  have hbound : ∀ n, |t (n + N)| ≤ B := fun n =>
    hUsub (hN (n + N) (Nat.le_add_left N n)) (t (n + N)) (ht (n + N))
  -- Bolzano–Weierstrass: pass to a convergent subsequence of the second coordinates.
  obtain ⟨a, -, φ, hφmono, hφtend⟩ :=
    (isCompact_Icc (a := -B) (b := B)).tendsto_subseq (x := fun n => t (n + N))
      (fun n => abs_le.mp (hbound n))
  have hv' : Tendsto (fun m => v (φ m + N)) atTop (𝓝 x) :=
    ((Filter.tendsto_add_atTop_iff_nat N).mpr hvx).comp hφmono.tendsto_atTop
  have hprod : Tendsto (fun m => (v (φ m + N), t (φ m + N))) atTop (𝓝 (x, a)) :=
    hv'.prodMk_nhds hφtend
  exact ⟨a,
    hD.mem_of_tendsto hprod (Eventually.of_forall fun n => hAD (ht (φ n + N))),
    hS.mem_of_tendsto hprod (Eventually.of_forall fun n => hAS (ht (φ n + N)))⟩

end Work.WilE4.CAD
