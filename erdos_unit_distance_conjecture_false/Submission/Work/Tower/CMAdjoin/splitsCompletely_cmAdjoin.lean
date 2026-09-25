import Mathlib
import Submission.Work.Tower.CMAdjoin.Basic
import Submission.Work.Tower.CMAdjoin.SplitsIntoTwo
import Submission.Work.Tower.CMAdjoin.exists_two_primes_over
import Submission.Work.Defs.Basic

namespace Work.Tower.CMAdjoin

open NumberField

set_option maxHeartbeats 1000000

theorem splitsCompletely_cmAdjoin (L : Type*) [Field L] [NumberField L]
    [NumberField.IsTotallyReal L] (q : ℕ) (hq : q.Prime) (h4 : q % 4 = 1)
    (hL : Work.Defs.SplitsCompletely q L) :
    Work.Defs.SplitsCompletely q (Work.Tower.CMAdjoin.cmAdjoin L) := by
  classical
  rw [Work.Defs.SplitsCompletely] at hL ⊢
  obtain ⟨𝔮, hprime, hqmem, hres, hincomp, hprod⟩ := hL
  -- split each prime of `𝓞 L` above `q`
  have hsplit : ∀ i, SplitsIntoTwo L q (𝔮 i) := fun i =>
    exists_two_primes_over L q hq h4 (𝔮 i) (hprime i) (hres i)
  unfold SplitsIntoTwo at hsplit
  choose 𝔔₀ 𝔔₁ hφ using hsplit
  have hφ0prime : ∀ i, (𝔔₀ i).IsPrime := fun i => (hφ i).1
  have hφ1prime : ∀ i, (𝔔₁ i).IsPrime := fun i => (hφ i).2.1
  have hφne : ∀ i, 𝔔₀ i ≠ 𝔔₁ i := fun i => (hφ i).2.2.1
  have hφ0lies : ∀ i, (𝔔₀ i).LiesOver (𝔮 i) := fun i => (hφ i).2.2.2.1
  have hφ1lies : ∀ i, (𝔔₁ i).LiesOver (𝔮 i) := fun i => (hφ i).2.2.2.2.1
  have hφ0res : ∀ i, Nonempty (𝓞 (cmAdjoin L) ⧸ 𝔔₀ i ≃+* ZMod q) :=
    fun i => (hφ i).2.2.2.2.2.1
  have hφ1res : ∀ i, Nonempty (𝓞 (cmAdjoin L) ⧸ 𝔔₁ i ≃+* ZMod q) :=
    fun i => (hφ i).2.2.2.2.2.2.1
  have hφmap : ∀ i, (𝔮 i).map (algebraMap (𝓞 L) (𝓞 (cmAdjoin L))) = 𝔔₀ i * 𝔔₁ i :=
    fun i => (hφ i).2.2.2.2.2.2.2
  -- the two primes over `𝔮 i`, indexed by `Fin 2`
  let W : Fin (Module.finrank ℚ L) → Fin 2 → Ideal (𝓞 (cmAdjoin L)) :=
    fun i j => if j = 0 then 𝔔₀ i else 𝔔₁ i
  have W0 : ∀ i, W i 0 = 𝔔₀ i := fun i => by dsimp only [W]; rw [ite_eq_left rfl]
  have W1 : ∀ i, W i 1 = 𝔔₁ i := fun i => by dsimp only [W]; rw [ite_eq_right (by decide)]
  have Wprime : ∀ i j, (W i j).IsPrime := by
    intro i j
    by_cases h : j = 0
    · rw [show W i j = 𝔔₀ i by dsimp only [W]; rw [ite_eq_left h]]; exact hφ0prime i
    · rw [show W i j = 𝔔₁ i by dsimp only [W]; rw [ite_eq_right h]]; exact hφ1prime i
  have Wqmem : ∀ i j, (q : 𝓞 (cmAdjoin L)) ∈ W i j := by
    intro i j
    by_cases h : j = 0
    · rw [show W i j = 𝔔₀ i by dsimp only [W]; rw [ite_eq_left h]]
      haveI := hφ0lies i
      have hh := (Ideal.mem_of_liesOver (𝔔₀ i) (𝔮 i) (q : 𝓞 L)).mp (hqmem i)
      simpa using hh
    · rw [show W i j = 𝔔₁ i by dsimp only [W]; rw [ite_eq_right h]]
      haveI := hφ1lies i
      have hh := (Ideal.mem_of_liesOver (𝔔₁ i) (𝔮 i) (q : 𝓞 L)).mp (hqmem i)
      simpa using hh
  have Wres : ∀ i j, Nonempty (𝓞 (cmAdjoin L) ⧸ W i j ≃+* ZMod q) := by
    intro i j
    by_cases h : j = 0
    · rw [show W i j = 𝔔₀ i by dsimp only [W]; rw [ite_eq_left h]]; exact hφ0res i
    · rw [show W i j = 𝔔₁ i by dsimp only [W]; rw [ite_eq_right h]]; exact hφ1res i
  have Wcomap : ∀ i j, Ideal.comap (algebraMap (𝓞 L) (𝓞 (cmAdjoin L))) (W i j) = 𝔮 i := by
    intro i j
    by_cases h : j = 0
    · rw [show W i j = 𝔔₀ i by dsimp only [W]; rw [ite_eq_left h]]
      haveI := hφ0lies i
      refine Ideal.ext (fun x => ?_)
      rw [Ideal.mem_comap]
      exact (Ideal.mem_of_liesOver (𝔔₀ i) (𝔮 i) x).symm
    · rw [show W i j = 𝔔₁ i by dsimp only [W]; rw [ite_eq_right h]]
      haveI := hφ1lies i
      refine Ideal.ext (fun x => ?_)
      rw [Ideal.mem_comap]
      exact (Ideal.mem_of_liesOver (𝔔₁ i) (𝔮 i) x).symm
  -- the reindexing `Fin n × Fin 2 ≃ Fin (2n)`
  let e : Fin (Module.finrank ℚ L) × Fin 2 ≃ Fin (Module.finrank ℚ (cmAdjoin L)) :=
    (finProdFinEquiv.trans (finCongr (Nat.mul_comm (Module.finrank ℚ L) 2))).trans
      (finCongr (finrank_cmAdjoin_rat L).symm)
  let 𝔙 : Fin (Module.finrank ℚ (cmAdjoin L)) → Ideal (𝓞 (cmAdjoin L)) :=
    fun k => W (e.symm k).1 (e.symm k).2
  have hVprime : ∀ k, (𝔙 k).IsPrime := fun k => Wprime (e.symm k).1 (e.symm k).2
  have hVqmem : ∀ k, (q : 𝓞 (cmAdjoin L)) ∈ 𝔙 k :=
    fun k => Wqmem (e.symm k).1 (e.symm k).2
  have hVres : ∀ k, Nonempty (𝓞 (cmAdjoin L) ⧸ 𝔙 k ≃+* ZMod q) :=
    fun k => Wres (e.symm k).1 (e.symm k).2
  -- `W` (hence `𝔙`) is injective on `Fin n × Fin 2`
  have W_inj : ∀ x y : Fin (Module.finrank ℚ L) × Fin 2,
      W x.1 x.2 = W y.1 y.2 → x = y := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hW
    have hii : i = i' := by
      by_contra hne
      have hc1 := Wcomap i j
      have hc2 := Wcomap i' j'
      rw [hW] at hc1
      rw [hc1] at hc2
      exact hincomp i i' hne (le_of_eq hc2)
    subst hii
    congr 1
    by_contra hne
    have hj2 : j = 0 ∨ j = 1 := by fin_cases j <;> simp
    have hj2' : j' = 0 ∨ j' = 1 := by fin_cases j' <;> simp
    rcases hj2 with hj | hj <;> rcases hj2' with hj' | hj'
    · exact hne (hj.trans hj'.symm)
    · rw [hj, hj', W0, W1] at hW; exact hφne i hW
    · rw [hj, hj', W0, W1] at hW; exact hφne i hW.symm
    · exact hne (hj.trans hj'.symm)
  have hVinj : Function.Injective 𝔙 := by
    intro k k' hkk
    have hxy : e.symm k = e.symm k' := W_inj _ _ hkk
    exact e.symm.injective hxy
  have hVbot : ∀ k, 𝔙 k ≠ ⊥ := by
    intro k h
    have hmem : (q : 𝓞 (cmAdjoin L)) ∈ (⊥ : Ideal (𝓞 (cmAdjoin L))) :=
      h ▸ hVqmem k
    rw [Ideal.mem_bot] at hmem
    exact hq.ne_zero (by exact_mod_cast hmem)
  have hVmax : ∀ k, (𝔙 k).IsMaximal := fun k => (hVprime k).isMaximal (hVbot k)
  have hVincomp : ∀ k k', k ≠ k' → ¬ 𝔙 k ≤ 𝔙 k' := by
    intro k k' hne hle
    have heq : 𝔙 k = 𝔙 k' := (hVmax k).eq_of_le (hVmax k').ne_top hle
    exact hne (hVinj heq)
  -- the product formula
  have hmap_prod : ∀ (s : Finset (Fin (Module.finrank ℚ L))),
      Ideal.map (algebraMap (𝓞 L) (𝓞 (cmAdjoin L))) (∏ i ∈ s, 𝔮 i) =
        ∏ i ∈ s, Ideal.map (algebraMap (𝓞 L) (𝓞 (cmAdjoin L))) (𝔮 i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        rw [Finset.prod_empty, Finset.prod_empty,
          show (1 : Ideal (𝓞 L)) = ⊤ from Ideal.one_eq_top, Ideal.map_top,
          show (⊤ : Ideal (𝓞 (cmAdjoin L))) = 1 from Ideal.one_eq_top.symm]
    | insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha, Ideal.map_mul, ih]
  have key : ∀ i, (𝔮 i).map (algebraMap (𝓞 L) (𝓞 (cmAdjoin L))) = ∏ j : Fin 2, W i j := by
    intro i
    rw [hφmap i, Fin.prod_univ_two, W0 i, W1 i]
  have hprodV :
      Ideal.span ({(q : 𝓞 (cmAdjoin L))} : Set (𝓞 (cmAdjoin L))) = ∏ k, 𝔙 k := by
    calc Ideal.span ({(q : 𝓞 (cmAdjoin L))} : Set (𝓞 (cmAdjoin L)))
        = Ideal.map (algebraMap (𝓞 L) (𝓞 (cmAdjoin L)))
            (Ideal.span ({(q : 𝓞 L)} : Set (𝓞 L))) := by
          rw [Ideal.map_span, Set.image_singleton, map_natCast]
      _ = Ideal.map (algebraMap (𝓞 L) (𝓞 (cmAdjoin L))) (∏ i, 𝔮 i) := by rw [← hprod]
      _ = ∏ i : Fin (Module.finrank ℚ L),
            (𝔮 i).map (algebraMap (𝓞 L) (𝓞 (cmAdjoin L))) := hmap_prod Finset.univ
      _ = ∏ i : Fin (Module.finrank ℚ L), ∏ j : Fin 2, W i j :=
            Finset.prod_congr rfl (fun i _ => key i)
      _ = ∏ x : Fin (Module.finrank ℚ L) × Fin 2, W x.1 x.2 :=
            (Fintype.prod_prod_type (fun x => W x.1 x.2)).symm
      _ = ∏ k : Fin (Module.finrank ℚ (cmAdjoin L)), 𝔙 k :=
            Fintype.prod_equiv e (fun x => W x.1 x.2) (fun k => 𝔙 k)
              (fun x => by simp only [𝔙, Equiv.symm_apply_apply])
  exact ⟨𝔙, hVprime, hVqmem, hVres, hVincomp, hprodV⟩

end Work.Tower.CMAdjoin
