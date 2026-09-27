import Mathlib
import Submission.Work.Surf.zeroSet_persist_one_dim

namespace Work.Surf

open Set Filter

open scoped Topology

/-- **At most one zero of a `C¹` function with nowhere-vanishing derivative on an interval.**
If `deriv g'` is non-zero on `Icc a b`, then `g'` has at most one zero in `Ioo a b` (two of them
would give, by Rolle's theorem, a point of `Ioo a b` where `deriv g'` vanishes). -/
lemma rayp_subsingleton_zeros {g' : ℝ → ℝ} (hg' : ContDiff ℝ 1 g') {a b : ℝ}
    (hne : ∀ c ∈ Set.Icc a b, deriv g' c ≠ 0) :
    (({t : ℝ | g' t = 0}) ∩ Set.Ioo a b).Subsingleton := by
  intro x hx y hy
  by_contra hxy
  rcases lt_or_gt_of_ne hxy with hlt | hlt
  · obtain ⟨c, hc, hc0⟩ := exists_deriv_eq_zero hlt hg'.continuous.continuousOn
      (by rw [hx.1, hy.1])
    exact hne c ⟨by linarith [hc.1, hx.2.1], by linarith [hc.2, hy.2.2]⟩ hc0
  · obtain ⟨c, hc, hc0⟩ := exists_deriv_eq_zero hlt hg'.continuous.continuousOn
      (by rw [hy.1, hx.1])
    exact hne c ⟨by linarith [hc.1, hy.2.1], by linarith [hc.2, hx.2.2]⟩ hc0



/-- **Persistence of the ray-meeting set of a one-dimensional pair, from a *separation* hypothesis.**
Variant of `Work.Surf.zeroSet_persist_one_dim` in which the "anti-ray" bound `hanti` is replaced by
the weaker *separation* hypothesis `hsep`, and in which the conclusion is strengthened by the
regularity clause `deriv g' ≠ 0` on the perturbed ray-meeting set (instead of equality of
cardinalities).

Proof (see the discussion in the module docstring of `zeroSet_persist_one_dim`): put
`S := {t ∈ Icc 0 1 | g t = 0 ∧ 0 < h t}`.  For `p ∈ S` (so `p ∈ Ioo 0 1` and `deriv g p ≠ 0`) choose
`e p > 0` with `e p ≤ min (p/2) ((1-p)/2)`, `|deriv g p|/2 ≤ |deriv g s|` for `s ∈ Icc (p - e p) (p + e p)`
(this is `Work.Surf.zsp_simple_interval`).  Let `μ > 0` be a lower bound of `p ↦ e p / 2` on the
finite set `S` and `ν > 0` a lower bound of `p ↦ |deriv g p| / 4`
(`Work.Surf.zsp_exists_pos_le_of_finite`; use a total function with the value `1` off `S` so that the
case `S = ∅` needs no separate treatment).  Apply `hsep` with `ε := μ` to get `δA > 0`, and set
`δ := min δA ν`.  For `g'`, `h'` `δ`-close, every `t` in the new ray set `S'` satisfies
`|g t| ≤ δA` and `-δA ≤ h t`, so `hsep` gives `p ∈ S` with `|t - p| < μ ≤ e p`, i.e.
`t ∈ Ioo (p - e p) (p + e p) ⊆ Ioo 0 1`: this gives the containment in `(0,1)` and the transversality
`|deriv g' t| ≥ |deriv g p|/2 - ν ≥ |deriv g p|/4 > 0`.  Finally `S'` is contained in the union over
the finite set `S` of the intervals `Ioo (p - e p) (p + e p)`, and each of these contains at most one
point of `S'` (two zeros of `g'` in such an interval would give, by Rolle's theorem, a point `c` with
`deriv g' c = 0`, contradicting the bound `|deriv g' c| ≥ |deriv g p|/4 > 0`); hence `S'` is finite.
Note for `S = ∅` the argument is uniform: `hsep` then says exactly that no `t ∈ [0,1]` has
`|g t| ≤ δA` and `h t ≥ -δA`, so `S' = ∅`.

(Remark on the rejected review: the counterexample proposed there takes the perturbation equal to the
gap `c` while also taking `δ > c`; but in this statement `δ` is *chosen* by the producer of the
witness, and `hsep` permits the choice `δ ≤ δA`, where `δA` is exactly the threshold below which no
"near-ray" point survives.  A perturbation of size `< δ ≤ c` cannot create a zero of `g'` when
`g ≥ c > 0`.) -/
theorem raySet_persist_one_dim
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g) (h : ℝ → ℝ)
    (hfin : ({t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ g t = 0 ∧ 0 < h t}).Finite)
    (hint : ({t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ g t = 0 ∧ 0 < h t}) ⊆ Set.Ioo (0 : ℝ) 1)
    (htrans : ∀ t ∈ Set.Icc (0 : ℝ) 1, g t = 0 → 0 < h t → deriv g t ≠ 0)
    (hsep : ∀ ε > 0, ∃ δA > 0, ∀ t ∈ Set.Icc (0 : ℝ) 1, |g t| ≤ δA → -δA ≤ h t →
      ∃ p ∈ {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ g t = 0 ∧ 0 < h t}, |t - p| < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (g' h' : ℝ → ℝ), ContDiff ℝ 1 g' →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, |g' t - g t| ≤ δ) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, |deriv g' t - deriv g t| ≤ δ) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, |h' t - h t| ≤ δ) →
      ({t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ g' t = 0 ∧ 0 < h' t}).Finite ∧
        ({t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ g' t = 0 ∧ 0 < h' t}) ⊆ Set.Ioo (0 : ℝ) 1 ∧
        (∀ t ∈ {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ g' t = 0 ∧ 0 < h' t}, deriv g' t ≠ 0) := by
  classical
  set S : Set ℝ := {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ g t = 0 ∧ 0 < h t} with hSdef
  have hSmem : ∀ t : ℝ, t ∈ S ↔ t ∈ Set.Icc (0 : ℝ) 1 ∧ g t = 0 ∧ 0 < h t := by
    intro t; rw [hSdef]; rfl
  have hSfin : S.Finite := by rw [hSdef]; exact hfin
  have hSint : S ⊆ Set.Ioo (0 : ℝ) 1 := by rw [hSdef]; exact hint
  have hdata : ∀ p ∈ S, ∃ e : ℝ, 0 < e ∧ e ≤ min (p / 2) ((1 - p) / 2) ∧
      (∀ s ∈ Set.Icc (p - e) (p + e), |deriv g p| / 2 ≤ |deriv g s|) := by
    intro p hp
    obtain ⟨hpinIcc, hg0, hh0⟩ := (hSmem p).mp hp
    have hpin : p ∈ Set.Ioo (0 : ℝ) 1 := hSint hp
    have hd : deriv g p ≠ 0 := htrans p hpinIcc hg0 hh0
    have hR : 0 < min (p / 2) ((1 - p) / 2) := lt_min (by linarith [hpin.1]) (by linarith [hpin.2])
    obtain ⟨e, hepos, heR, hA, -⟩ := zsp_simple_interval g hg hg0 hd hR
    exact ⟨e, hepos, heR, hA⟩
  choose e he using hdata
  let ef : ℝ → ℝ := fun p => if hp : p ∈ S then e p hp else 1
  have hef : ∀ (p : ℝ) (hp : p ∈ S), ef p = e p hp := fun p hp => dif_pos hp
  have hefpos : ∀ p ∈ S, 0 < ef p := fun p hp => by rw [hef p hp]; exact (he p hp).1
  have hefle : ∀ p ∈ S, ef p ≤ min (p / 2) ((1 - p) / 2) :=
    fun p hp => by rw [hef p hp]; exact (he p hp).2.1
  have hderivlb : ∀ p ∈ S, ∀ s ∈ Set.Icc (p - ef p) (p + ef p),
      |deriv g p| / 2 ≤ |deriv g s| := fun p hp => by rw [hef p hp]; exact (he p hp).2.2
  have hsubI : ∀ p ∈ S, Set.Icc (p - ef p) (p + ef p) ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro p hp s hs
    have he1 : ef p ≤ p / 2 := le_trans (hefle p hp) (min_le_left _ _)
    have he2 : ef p ≤ (1 - p) / 2 := le_trans (hefle p hp) (min_le_right _ _)
    have hp1 : 0 < p := (hSint hp).1
    have hp2 : p < 1 := (hSint hp).2
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  obtain ⟨μ, hμpos, hμ⟩ := zsp_exists_pos_le_of_finite hSfin (f := fun p => ef p / 2)
    (fun p hp => by have h := hefpos p hp; linarith)
  obtain ⟨ν, hνpos, hν⟩ := zsp_exists_pos_le_of_finite hSfin (f := fun p => |deriv g p| / 4)
    (fun p hp => by
      have hd : deriv g p ≠ 0 :=
        htrans p ((hSmem p).mp hp).1 ((hSmem p).mp hp).2.1 ((hSmem p).mp hp).2.2
      exact div_pos (abs_pos.mpr hd) (by norm_num))
  obtain ⟨δA, hδApos, hA⟩ := hsep μ hμpos
  refine ⟨min δA ν, lt_min hδApos hνpos, ?_⟩
  intro g' h' hg' hcl1 hcl2 hcl3
  set S' : Set ℝ := {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ g' t = 0 ∧ 0 < h' t} with hS'def
  have hS'mem : ∀ t : ℝ, t ∈ S' ↔ t ∈ Set.Icc (0 : ℝ) 1 ∧ g' t = 0 ∧ 0 < h' t := by
    intro t; rw [hS'def]; rfl
  -- Every point of `S'` is close to a point of `S`, and lies in the corresponding interval.
  have hcover : ∀ t ∈ S', ∃ p ∈ S, t ∈ Set.Ioo (p - ef p) (p + ef p) := by
    intro t ht
    obtain ⟨htIcc, htg', hth'⟩ := (hS'mem t).mp ht
    have h1 : |g t| ≤ δA := by
      have hh := hcl1 t htIcc
      rw [htg', zero_sub, abs_neg] at hh
      linarith [min_le_left δA ν]
    have h2 : -δA ≤ h t := by
      have hh := hcl3 t htIcc
      have hh2 := (abs_le.mp hh).2
      linarith [min_le_left δA ν]
    obtain ⟨p, hp, hpt⟩ := hA t htIcc h1 h2
    have hle : μ ≤ ef p :=
      le_trans (hμ p ((hSmem p).mpr hp)) (by linarith [hefpos p ((hSmem p).mpr hp)])
    have hlt := abs_lt.mp (lt_of_lt_of_le hpt hle)
    exact ⟨p, (hSmem p).mpr hp, ⟨by linarith [hlt.1], by linarith [hlt.2]⟩⟩
  -- On each of the intervals, `g'` has at most one zero.
  have hderiv'_ne : ∀ p ∈ S, ∀ c ∈ Set.Icc (p - ef p) (p + ef p), deriv g' c ≠ 0 := by
    intro p hp c hc
    have hcIcc : c ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self (hsubI p hp hc)
    have h1 : |deriv g p| / 2 ≤ |deriv g c| := hderivlb p hp c hc
    have h2 : |deriv g' c - deriv g c| ≤ min δA ν := hcl2 c hcIcc
    have h3 : min δA ν ≤ |deriv g p| / 4 := le_trans (min_le_right δA ν) (hν p hp)
    have h4 : 0 < |deriv g p| :=
      abs_pos.mpr (htrans p ((hSmem p).mp hp).1 ((hSmem p).mp hp).2.1 ((hSmem p).mp hp).2.2)
    intro h0
    rw [h0, zero_sub, abs_neg] at h2
    linarith
  have hpiece : ∀ p ∈ S, (S' ∩ Set.Ioo (p - ef p) (p + ef p)).Subsingleton := by
    intro p hp
    have hsub : S' ∩ Set.Ioo (p - ef p) (p + ef p)
        ⊆ ({t : ℝ | g' t = 0}) ∩ Set.Ioo (p - ef p) (p + ef p) := by
      intro t ht
      exact ⟨((hS'mem t).mp ht.1).2.1, ht.2⟩
    intro x hx y hy
    exact rayp_subsingleton_zeros hg' (fun c hc => hderiv'_ne p hp c hc) (hsub hx) (hsub hy)
  have hcov : S' ⊆ ⋃ p ∈ S, (S' ∩ Set.Ioo (p - ef p) (p + ef p)) := by
    intro t ht
    obtain ⟨p, hp, hmem⟩ := hcover t ht
    exact Set.mem_iUnion₂.mpr ⟨p, hp, ht, hmem⟩
  have hfinU : (⋃ p ∈ S, (S' ∩ Set.Ioo (p - ef p) (p + ef p))).Finite :=
    Set.Finite.biUnion hSfin (fun p hp => (hpiece p hp).finite)
  refine ⟨hfinU.subset hcov, ?_, ?_⟩
  · intro t ht
    obtain ⟨p, hp, hmem⟩ := hcover t ht
    exact hsubI p hp (Set.Ioo_subset_Icc_self hmem)
  · intro t ht
    obtain ⟨p, hp, hmem⟩ := hcover t ht
    exact hderiv'_ne p hp t (Set.Ioo_subset_Icc_self hmem)


end Work.Surf
