import Mathlib
import Submission.Work.Repel.invFunOn_differentiableOn

namespace Work.Horn.HB

open Set Metric Filter Topology

/-- A map `G` that is a bijection of `U` and a holomorphic `Φ` with the Abel relation
`Φ (G z) = Φ z + 1` on `U` cannot have a subset `P` on which `Φ` is injective, which is
forward `G`-invariant, which *enters* every orbit, and whose `Φ`-image contains right
half-strips of every height (`hstrip`), when `U` is bounded.

The proof: the Abel relation makes `Φ '' U` invariant under translation by `1`, and the
bijectivity of `G` on `U` makes it invariant under translation by `-1`.  Combined with
`hstrip` (applied to the `Φ`-image of `P`) this forces `Φ '' U = ℂ`.  Then the entering
condition `henter`, injectivity of `Φ` on `P` and `G '' P ⊆ P` force `Φ` to be injective
on all of `U`, so `Φ : U → ℂ` is a holomorphic bijection from the bounded set `U` onto
`ℂ`; its inverse would be an entire bounded function, hence constant by Liouville, which
is impossible because `U` is a nonempty open set. -/
theorem false_of_abel_spread {G : ℂ → ℂ} {U P : Set ℂ} {Φ : ℂ → ℂ}
    (hUopen : IsOpen U) (hbdd : Bornology.IsBounded U) (hPsub : P ⊆ U)
    (hmap : Set.MapsTo G U U) (hsurj : U ⊆ G '' U) (hinj : Set.InjOn G U)
    (hPmap : G '' P ⊆ P)
    (hΦdiff : DifferentiableOn ℂ Φ U) (habel : ∀ z ∈ U, Φ (G z) = Φ z + 1)
    (hΦinj : Set.InjOn Φ P)
    (hstrip : ∀ b : ℝ, ∃ C : ℝ, ∀ w : ℂ, C < w.re → |w.im| ≤ b → ∃ z ∈ P, Φ z = w)
    (henter : ∀ z ∈ U, ∃ n : ℕ, G^[n] z ∈ P) : False := by
  classical
  -- iterates of `G` stay in `U` and are injective there
  have hiter_mem : ∀ (n : ℕ) (z : ℂ), z ∈ U → G^[n] z ∈ U := by
    intro n
    induction n with
    | zero => intro z hz; simpa using hz
    | succ n ih => intro z hz; rw [Function.iterate_succ_apply' G n z]; exact hmap (ih z hz)
  have hiter_inj : ∀ n : ℕ, Set.InjOn (G^[n]) U := by
    intro n
    induction n with
    | zero => intro x hx y hy h; simpa using h
    | succ n ih =>
      intro x hx y hy h
      rw [Function.iterate_succ_apply' G n x, Function.iterate_succ_apply' G n y] at h
      exact ih hx hy (hinj (hiter_mem n x hx) (hiter_mem n y hy) h)
  -- the Abel relation iterated
  have habel_iter : ∀ (n : ℕ) (z : ℂ), z ∈ U → Φ (G^[n] z) = Φ z + (n : ℂ) := by
    intro n
    induction n with
    | zero => intro z hz; simp
    | succ n ih =>
      intro z hz
      rw [Function.iterate_succ_apply' G n z, habel (G^[n] z) (hiter_mem n z hz), ih z hz]
      push_cast
      ring
  -- forward invariance of `P` under iterates of `G`
  have hPiter : ∀ (n : ℕ) (z : ℂ), z ∈ P → G^[n] z ∈ P := by
    intro n
    induction n with
    | zero => intro z hz; simpa using hz
    | succ n ih =>
      intro z hz
      rw [Function.iterate_succ_apply' G n z]
      exact hPmap (Set.mem_image_of_mem G (ih z hz))
  -- `Φ '' U` is invariant under translation by `-1`: use that `G : U → U` is onto.
  have hback : ∀ w ∈ Φ '' U, w - 1 ∈ Φ '' U := by
    rintro w ⟨z, hzU, rfl⟩
    obtain ⟨z', hz'U, hz'⟩ := hsurj hzU
    exact ⟨z', hz'U, by rw [← hz', habel z' hz'U]; ring⟩
  -- hence invariant under every negative integer translation
  have hshiftNeg : ∀ (n : ℕ) (u : ℂ), u ∈ Φ '' U → u - ((n : ℝ) : ℂ) ∈ Φ '' U := by
    intro n
    induction n with
    | zero => intro u hu; simpa using hu
    | succ n ih =>
      intro u hu
      have h1 : (u - ((n:ℝ):ℂ)) - 1 ∈ Φ '' U := hback _ (ih u hu)
      have heq : u - (((n+1 : ℕ):ℝ):ℂ) = (u - ((n:ℝ):ℂ)) - 1 := by push_cast; ring
      rwa [heq]
  -- `hstrip` then forces `Φ '' U = ℂ`
  have huniv : ∀ w : ℂ, w ∈ Φ '' U := by
    intro w
    obtain ⟨C, hC⟩ := hstrip |w.im|
    obtain ⟨n, hn⟩ := exists_nat_gt (C - w.re)
    set u : ℂ := w + ((n:ℝ):ℂ) with hu
    have hure : u.re = w.re + n := by simp [hu]
    have huim : u.im = w.im := by simp [hu]
    have hre : C < u.re := by rw [hure]; linarith
    have him : |u.im| ≤ |w.im| := by rw [huim]
    obtain ⟨z, hzP, hzΦ⟩ := hC u hre him
    have hmem : u ∈ Φ '' U := ⟨z, hPsub hzP, hzΦ⟩
    have heq : w = u - ((n:ℝ):ℂ) := by rw [hu]; ring
    rw [heq]
    exact hshiftNeg n u hmem
  -- `Φ` is injective on all of `U`
  have hΦinjU : Set.InjOn Φ U := by
    have key : ∀ (a b : ℂ) (m₁ m₂ : ℕ), a ∈ U → b ∈ U → Φ a = Φ b →
        G^[m₁] a ∈ P → G^[m₂] b ∈ P → m₁ ≤ m₂ → a = b := by
      intro a b m₁ m₂ ha hb hab hpa hpb hle
      rcases lt_or_eq_of_le hle with hlt | hsubst
      · set k := m₂ - m₁ with hk
        have hsum : k + m₁ = m₂ := by omega
        have hq : G^[k] (G^[m₁] a) ∈ P := hPiter k (G^[m₁] a) hpa
        have hvalq : Φ (G^[k] (G^[m₁] a)) = Φ a + (m₂ : ℂ) := by
          rw [← Function.iterate_add_apply G k m₁ a, hsum, habel_iter m₂ a ha]
        have hvalb : Φ (G^[m₂] b) = Φ a + (m₂ : ℂ) := by
          rw [habel_iter m₂ b hb, ← hab]
        have hEq : G^[k] (G^[m₁] a) = G^[m₂] b := hΦinj hq hpb (by rw [hvalq, hvalb])
        have hEq2 : G^[m₂] a = G^[m₂] b := by
          rw [← Function.iterate_add_apply G k m₁ a, hsum] at hEq
          exact hEq
        exact hiter_inj m₂ ha hb hEq2
      · subst hsubst
        have hEq : G^[m₁] a = G^[m₁] b :=
          hΦinj hpa hpb (by rw [habel_iter m₁ a ha, habel_iter m₁ b hb, hab])
        exact hiter_inj m₁ ha hb hEq
    intro z₁ hz₁ z₂ hz₂ heq
    obtain ⟨n₁, hn₁⟩ := henter z₁ hz₁
    obtain ⟨n₂, hn₂⟩ := henter z₂ hz₂
    rcases le_total n₁ n₂ with hle | hle
    · exact key z₁ z₂ n₁ n₂ hz₁ hz₂ heq hn₁ hn₂ hle
    · exact (key z₂ z₁ n₂ n₁ hz₂ hz₁ heq.symm hn₂ hn₁ hle).symm
  -- Liouville: the inverse of `Φ` would be entire and bounded
  have huniv_image : Φ '' U = Set.univ := Set.eq_univ_iff_forall.mpr huniv
  have hΨdiff : DifferentiableOn ℂ (Function.invFunOn Φ U) (Φ '' U) :=
    Work.Repel.invFunOn_differentiableOn hUopen hΦinjU hΦdiff
  have hΨdiff' : DifferentiableOn ℂ (Function.invFunOn Φ U) Set.univ := by
    rwa [huniv_image] at hΨdiff
  have hΨmem : ∀ w : ℂ, Function.invFunOn Φ U w ∈ U := by
    intro w
    have hw : w ∈ Φ '' U := by rw [huniv_image]; exact Set.mem_univ w
    obtain ⟨z, hzU, hz⟩ := hw
    exact Function.invFunOn_mem ⟨z, hzU, hz⟩
  have hΨbdd : Bornology.IsBounded (Set.range (Function.invFunOn Φ U)) :=
    hbdd.subset (Set.range_subset_iff.mpr hΨmem)
  obtain ⟨c, hc⟩ :=
    (differentiableOn_univ.mp hΨdiff').exists_const_forall_eq_of_bounded hΨbdd
  have hUsub : U ⊆ {c} := by
    intro z hz
    have h1 : Function.invFunOn Φ U (Φ z) = z := by
      have h2 : Φ (Function.invFunOn Φ U (Φ z)) = Φ z := Function.invFunOn_eq ⟨z, hz, rfl⟩
      exact hΦinjU (Function.invFunOn_mem ⟨z, hz, rfl⟩) hz h2
    rw [Set.mem_singleton_iff, ← h1]
    exact hc (Φ z)
  -- a second point of `U` contradicts `U ⊆ {c}`
  have hUne : U.Nonempty := by
    obtain ⟨C, hC⟩ := hstrip 0
    obtain ⟨z, hzP, -⟩ := hC ((C + 1 : ℝ) : ℂ)
      (by rw [Complex.ofReal_re]; linarith)
      (by simp)
    exact ⟨z, hPsub hzP⟩
  obtain ⟨z₀, hz₀⟩ := hUne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hUopen z₀ hz₀
  have hmem : z₀ + ((r/2 : ℝ) : ℂ) ∈ U := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    rw [show (z₀ + ((r/2:ℝ):ℂ)) - z₀ = ((r/2:ℝ):ℂ) from add_sub_cancel_left _ _]
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    linarith
  have h1 : z₀ + ((r/2:ℝ):ℂ) = c := hUsub hmem
  have h2 : z₀ = c := hUsub hz₀
  have h3 : z₀ + ((r/2:ℝ):ℂ) = z₀ := by rw [h1, ← h2]
  have h4 : ((r/2 : ℝ) : ℂ) = 0 := add_eq_left.mp h3
  have h5 : r/2 = 0 := Complex.ofReal_eq_zero.mp h4
  linarith

end Work.Horn.HB
