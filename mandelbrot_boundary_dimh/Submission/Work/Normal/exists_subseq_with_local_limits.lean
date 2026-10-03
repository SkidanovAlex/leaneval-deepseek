import Mathlib
import Submission.Work.Normal.Basic
import Submission.Work.Normal.isNormalFamily_of_tendsto_iterate

/-!
# A diagonal subsequence with local limits on a sequence of normal sets

Let `Fam` be a family of functions `ℂ → ℂ` which is normal on each set `G k` (each sequence of
members of `Fam` has a strictly monotone subsequence converging locally uniformly on `G k`, either
to a limit function or to the constant `∞`).  Then any sequence `v` of members of `Fam` admits a
single strictly monotone extraction `φ` such that, for **every** `k` simultaneously, the
subsequence `v ∘ φ` either converges locally uniformly on `G k` or tends to `∞` locally uniformly
on `G k`.

The proof is the classical nested-subsequence diagonal.  We build strictly monotone extractions
`Ψ 0 = id`, `Ψ (k+1) = Ψ k ∘ σ k`, where `σ k` is chosen so that `v ∘ Ψ (k+1)` converges on `G k`
(in one of the two senses), and set `φ k = Ψ k k`.  Since `Ψ (k+1)` is obtained from `Ψ k` by
composition with a strictly increasing map, every later `Ψ j` refines `Ψ k`; consequently the tail
`j ≥ k+1` of `φ` is a subsequence of `Ψ (k+1)`, and both notions of local limit are preserved under
reindexing and under changing finitely many terms of the sequence.
-/

namespace Work.Normal

open Filter Set Topology Function
open scoped Topology

/-- Local uniform divergence to `∞` is preserved by reindexing with a map tending to `atTop`. -/
theorem TendstoLocallyUniformlyAtTop.comp_index_atTop {F : ℕ → ℂ → ℂ} {U : Set ℂ} {τ : ℕ → ℕ}
    (h : TendstoLocallyUniformlyAtTop F U) (hτ : Tendsto τ atTop atTop) :
    TendstoLocallyUniformlyAtTop (fun n => F (τ n)) U := by
  intro K hKU hK R
  obtain ⟨N, hN⟩ := h K hKU hK R
  rw [tendsto_atTop_atTop] at hτ
  obtain ⟨a, ha⟩ := hτ N
  exact ⟨a, fun n hn z hz => hN (τ n) (ha n hn) z hz⟩

/-- Local uniform divergence to `∞` depends only on the eventual values of the sequence. -/
theorem TendstoLocallyUniformlyAtTop.congr_eventually {F G : ℕ → ℂ → ℂ} {U : Set ℂ}
    (h : TendstoLocallyUniformlyAtTop F U) (hFG : ∀ᶠ n in atTop, Set.EqOn (F n) (G n) U) :
    TendstoLocallyUniformlyAtTop G U := by
  intro K hKU hK R
  obtain ⟨N, hN⟩ := h K hKU hK R
  obtain ⟨N', hN'⟩ := eventually_atTop.mp hFG
  refine ⟨max N N', fun n hn z hz => ?_⟩
  rw [← hN' n (le_trans (le_max_right N N') hn) (hKU hz)]
  exact hN n (le_trans (le_max_left N N') hn) z hz

/-- Local uniform convergence depends only on the eventual values of the sequence. -/
theorem TendstoLocallyUniformlyOn.congr_eventually {F G : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (h : TendstoLocallyUniformlyOn F f atTop U)
    (hFG : ∀ᶠ n in atTop, Set.EqOn (F n) (G n) U) :
    TendstoLocallyUniformlyOn G f atTop U := by
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto] at h ⊢
  intro x hx
  obtain ⟨N, hN⟩ := eventually_atTop.mp hFG
  refine Filter.Tendsto.congr' ?_ (h x hx)
  refine Filter.eventually_of_mem
    (Filter.prod_mem_prod (eventually_atTop.mpr ⟨N, fun n hn => hn⟩) self_mem_nhdsWithin) ?_
  rintro ⟨n, z⟩ ⟨hn, hz⟩
  exact Prod.ext rfl (hN n hn hz)

theorem exists_subseq_with_local_limits {Fam : Set (ℂ → ℂ)} {v : ℕ → ℂ → ℂ}
    (hv : ∀ n, v n ∈ Fam) {G : ℕ → Set ℂ} (hGnorm : ∀ n, IsNormalFamily Fam (G n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k : ℕ,
      (∃ g : ℂ → ℂ, TendstoLocallyUniformlyOn (fun n => v (φ n)) g atTop (G k)) ∨
        TendstoLocallyUniformlyAtTop (fun n => v (φ n)) (G k) := by
  classical
  -- Normality on `G k`, applied to a reindexed sequence, gives a further extraction `σ`.
  have key : ∀ (ψ : ℕ → ℕ), StrictMono ψ → ∀ k : ℕ, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ((∃ g : ℂ → ℂ, TendstoLocallyUniformlyOn (fun n => v (ψ (σ n))) g atTop (G k)) ∨
        TendstoLocallyUniformlyAtTop (fun n => v (ψ (σ n))) (G k)) :=
    fun ψ _ k => hGnorm k (fun n => v (ψ n)) (fun n => hv (ψ n))
  let σOf : (k : ℕ) → (ψ : ℕ → ℕ) → StrictMono ψ → ℕ → ℕ :=
    fun k ψ hψ => Classical.choose (key ψ hψ k)
  have hσOf : ∀ k (ψ : ℕ → ℕ) (hψ : StrictMono ψ), StrictMono (σOf k ψ hψ) :=
    fun k ψ hψ => (Classical.choose_spec (key ψ hψ k)).1
  have hmodeOf : ∀ k (ψ : ℕ → ℕ) (hψ : StrictMono ψ),
      ((∃ g : ℂ → ℂ, TendstoLocallyUniformlyOn (fun n => v (ψ (σOf k ψ hψ n))) g atTop (G k)) ∨
        TendstoLocallyUniformlyAtTop (fun n => v (ψ (σOf k ψ hψ n))) (G k)) :=
    fun k ψ hψ => (Classical.choose_spec (key ψ hψ k)).2
  -- Nested subsequences `Ψ 0 = id`, `Ψ (k+1) = Ψ k ∘ σ k`, where `σ k` works on `G k`.
  let Ψ : ℕ → {ψ : ℕ → ℕ // StrictMono ψ} :=
    Nat.rec ⟨id, strictMono_id⟩ fun k prev =>
      ⟨prev.1 ∘ σOf k prev.1 prev.2, prev.2.comp (hσOf k prev.1 prev.2)⟩
  let σ : ℕ → ℕ → ℕ := fun k => σOf k (Ψ k).1 (Ψ k).2
  have hsucc : ∀ k, (Ψ (k+1)).1 = (Ψ k).1 ∘ σ k := fun k => rfl
  -- The two possible modes at level `k`.
  have hmode : ∀ k,
      ((∃ g : ℂ → ℂ, TendstoLocallyUniformlyOn (fun n => v ((Ψ (k+1)).1 n)) g atTop (G k)) ∨
        TendstoLocallyUniformlyAtTop (fun n => v ((Ψ (k+1)).1 n)) (G k)) :=
    fun k => by simpa only [hsucc k, Function.comp_apply] using hmodeOf k (Ψ k).1 (Ψ k).2
  -- The diagonal.
  let φ : ℕ → ℕ := fun k => (Ψ k).1 k
  have hφmono : StrictMono φ := by
    refine strictMono_nat_of_lt_succ fun m => ?_
    show (Ψ m).1 m < (Ψ (m+1)).1 (m+1)
    rw [hsucc m, Function.comp_apply]
    exact (Ψ m).2 (Nat.lt_of_lt_of_le (Nat.lt_succ_self m) ((hσOf m (Ψ m).1 (Ψ m).2).id_le (m+1)))
  -- Every later extraction refines an earlier one.
  have hrefine : ∀ m n, n ≤ m → ∀ k, ∃ j ≥ k, (Ψ m).1 k = (Ψ n).1 j := by
    intro m
    induction m with
    | zero =>
      intro n hn k
      obtain rfl : n = 0 := Nat.le_zero.mp hn
      exact ⟨k, le_rfl, rfl⟩
    | succ m ih =>
      intro n hn k
      rcases Nat.lt_or_ge n (m+1) with h | h
      · have hn' : n ≤ m := Nat.lt_succ_iff.mp h
        have hk : (Ψ (m+1)).1 k = (Ψ m).1 (σ m k) := by rw [hsucc m, Function.comp_apply]
        obtain ⟨j, hj, hjk⟩ := ih n hn' (σ m k)
        exact ⟨j, ((hσOf m (Ψ m).1 (Ψ m).2).id_le k).trans hj, by rw [hk, hjk]⟩
      · have hn'' : n = m+1 := le_antisymm hn h
        subst hn''
        exact ⟨k, le_rfl, rfl⟩
  -- Index map: `τ k m` is the position of `φ m` inside the extraction `Ψ (k+1)`.
  have hex : ∀ k m, ∃ j : ℕ, k + 1 ≤ m → (m ≤ j ∧ (Ψ m).1 m = (Ψ (k+1)).1 j) := by
    intro k m
    by_cases hm : k + 1 ≤ m
    · exact (hrefine m (k+1) hm m).imp (fun j hj => fun _ => hj)
    · exact ⟨0, fun h => absurd h hm⟩
  let τ : ℕ → ℕ → ℕ := fun k m => Classical.choose (hex k m)
  have hτ_spec : ∀ k m (hm : k + 1 ≤ m),
      m ≤ τ k m ∧ (Ψ m).1 m = (Ψ (k+1)).1 (τ k m) :=
    fun k m hm => Classical.choose_spec (hex k m) hm
  have hτ_tendsto : ∀ k, Tendsto (τ k) atTop atTop := by
    intro k
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨max b (k+1), fun m hm => ?_⟩
    exact le_trans (le_max_left b (k+1))
      (le_trans hm ((hτ_spec k m (le_trans (le_max_right b (k+1)) hm)).1))
  refine ⟨φ, hφmono, fun k => ?_⟩
  rcases hmode k with ⟨g, hg⟩ | hg
  · -- convergent mode on `G k`
    left
    refine ⟨g, ?_⟩
    have h1 : TendstoLocallyUniformlyOn (fun m => v ((Ψ (k+1)).1 (τ k m))) g atTop (G k) :=
      TendstoLocallyUniformlyOn.comp_strictMono_atTop
        (F := fun n => v ((Ψ (k+1)).1 n)) (φ := τ k) hg (hτ_tendsto k)
    refine TendstoLocallyUniformlyOn.congr_eventually h1 ?_
    refine eventually_atTop.mpr ⟨k+1, fun m hm => ?_⟩
    intro z hz
    show v ((Ψ (k+1)).1 (τ k m)) z = v ((Ψ m).1 m) z
    rw [(hτ_spec k m hm).2]
  · -- divergent mode on `G k`
    right
    have h1 : TendstoLocallyUniformlyAtTop (fun m => v ((Ψ (k+1)).1 (τ k m))) (G k) :=
      TendstoLocallyUniformlyAtTop.comp_index_atTop
        (F := fun n => v ((Ψ (k+1)).1 n)) (τ := τ k) hg (hτ_tendsto k)
    refine TendstoLocallyUniformlyAtTop.congr_eventually h1 ?_
    refine eventually_atTop.mpr ⟨k+1, fun m hm => ?_⟩
    intro z hz
    show v ((Ψ (k+1)).1 (τ k m)) z = v ((Ψ m).1 m) z
    rw [(hτ_spec k m hm).2]

end Work.Normal
