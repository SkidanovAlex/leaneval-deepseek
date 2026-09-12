import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Quotient.Basic

noncomputable section

open BigOperators

namespace Commons.LinearAlgebra.FreeModule

/-! # Extending a basis of a submodule to the whole module when the quotient is free

(`Basis` below is `Module.Basis`, i.e. `Module.Basis ι R N`.)

Let `N ≤ M` be a submodule of an arbitrary module over an arbitrary commutative ring
`R`, and suppose `N` has an `R`-basis `bN : Basis ι R N` and the quotient module
`M ⧸ N` has an `R`-basis `bQ : Basis κ R (M ⧸ N)`.  Then `bN` extends to an `R`-basis
`bM` of `M`: there is an `n : ℕ`, a basis `bM : Basis (Fin n) R M` and an embedding
`e : ι ↪ Fin n` such that `(bN i : M) = bM (e i)` for every `i` (the basis vectors of
`N` appear, in order, as an initial segment of the ambient basis — `bM` may simply be
taken over `Fin (Fintype.card ι + Fintype.card κ)` with the `N`-part first).

**Proof route (all Mathlib; no PID/domain hypotheses are needed — the freeness of the
quotient is supplied as data `bQ`):**
1. Section of the canonical surjection.  `p := N.mkQ : M →ₗ[R] M ⧸ N` is surjective
   (`Submodule.range_mkQ : p.range = ⊤`; turn this into `Function.Surjective p`, e.g.
   via `LinearMap.range_eq_top` / the surjectivity-iff-range theorem).  Choose for each
   `k : κ` a preimage `x k` of `bQ k` (Classical.choose of the surjectivity applied to
   `bQ k`), and define the section `s : (M ⧸ N) →ₗ[R] M` as the linear map sending
   `bQ k ↦ x k`, built with `(bQ.constr R) x` (see `Module.Basis.constr` /
   `Module.Basis.constr_basis`: `(bQ.constr R) x (bQ k) = x k`).  Then
   `p ∘ₗ s = LinearMap.id` by `Module.Basis.ext` (evaluate at each `bQ k`:
   `p (s (bQ k)) = p (x k) = bQ k`).
2. Splitting.  With `C := s.range ≤ M`: `N ⊔ C = ⊤` — for `x : M`,
   `x = (x - s (p x)) + s (p x)` with `p (x - s (p x)) = 0`, and `p.ker = N` by
   `Submodule.ker_mkQ`, so `x - s (p x) ∈ N`; and `N ⊓ C = ⊥` — if `y ∈ C` (say
   `y = s q`) and `y ∈ N`, then `p y = 0` (kernel) but also `p y = p (s q) = q`
   (`p ∘ₗ s = id`), so `q = 0`, `y = 0`.
3. Assemble the basis of `M`.  Let `n := Fintype.card ι + Fintype.card κ` and define the
   ambient family `w : Fin n → M` by putting `(bN i : M)` on the first `card ι` indices
   (`Fin.castAdd`/`Fin.addNat` split, or `Fin.append (fun i => (bN i : M))
   (fun k => s (bQ k))`).  `LinearIndependent R w`: a vanishing `R`-combination splits
   into its `N`-part and its `C`-part; applying `p` kills the `N`-part and maps the
   `C`-part to the corresponding `bQ`-combination (by `p ∘ₗ s = id`), whose vanishing is
   `bQ`-independence; the `N`-part then vanishes by `bN`-independence.  `⊤ ≤ span R
   (range w)`: by step 2, every `x = x_N + s q` with `x_N ∈ N = span (range
   (bN-coerced))` (`bN.span_eq`) and `q ∈ span (range bQ)` (`bQ.span_eq`), so
   `s q ∈ span (range w)`.  Conclude with `Module.Basis.mk`.  The required equality
   `(bN i : M) = bM (e i)` holds by construction with `e i := Fin.castLE
   (Nat.le_add_right _ _) i` (the first `card ι` positions).
-/
theorem basis_extend_of_quotient_free {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {N : Submodule R M} {ι : Type*} [Fintype ι]
    (bN : Module.Basis ι R N) {κ : Type*} [Fintype κ]
    (bQ : Module.Basis κ R (M ⧸ N)) :
    ∃ n : ℕ, ∃ bM : Module.Basis (Fin n) R M, ∃ e : ι ↪ Fin n,
      ∀ i : ι, (bN i : M) = bM (e i) := by
  classical
  -- Step 1 : section s of the canonical surjection p = N.mkQ.
  let p : M →ₗ[R] M ⧸ N := N.mkQ
  have hp_surj : Function.Surjective p := by
    rw [← LinearMap.range_eq_top]
    exact Submodule.range_mkQ N
  let x : κ → M := fun k => Classical.choose (hp_surj (bQ k))
  have hx : ∀ k : κ, p (x k) = bQ k := fun k => Classical.choose_spec (hp_surj (bQ k))
  let s : M ⧸ N →ₗ[R] M := (bQ.constr R) x
  have hsb : ∀ k : κ, s (bQ k) = x k := by
    intro k
    exact Module.Basis.constr_basis bQ R x k
  have hcomp : p.comp s = (LinearMap.id : M ⧸ N →ₗ[R] M ⧸ N) := by
    refine Module.Basis.ext bQ ?_
    intro k
    change p (s (bQ k)) = bQ k
    simp [hsb, hx]
  have hs : ∀ q : M ⧸ N, p (s q) = q := by
    intro q
    simpa [LinearMap.comp_apply] using congrArg (fun f : M ⧸ N →ₗ[R] M ⧸ N => f q) hcomp
  have hpker : p.ker = N := by
    change (N.mkQ).ker = N
    exact Submodule.ker_mkQ N
  -- Step 2 : N and C := s.range are complementary.
  let C : Submodule R M := s.range
  have hsup : N ⊔ C = ⊤ := by
    rw [Submodule.sup_eq_top_iff]
    intro m
    refine ⟨m - s (p m), ?_, s (p m), ?_, ?_⟩
    · have hp0 : p (m - s (p m)) = 0 := by
        calc
          p (m - s (p m)) = p m - p (s (p m)) := map_sub p m (s (p m))
          _ = p m - p m := by rw [hs (p m)]
          _ = 0 := sub_self (p m)
      have hmem : m - s (p m) ∈ p.ker := (LinearMap.mem_ker (f := p)).2 hp0
      simpa [hpker] using hmem
    · exact LinearMap.mem_range.mpr ⟨p m, rfl⟩
    · exact (sub_add_cancel m (s (p m))).symm
  have hinf : N ⊓ C = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hyNC
    rcases (Submodule.mem_inf.mp hyNC) with ⟨hyN, hyC⟩
    rcases (LinearMap.mem_range.mp hyC) with ⟨q, hq⟩
    have hpy : p y = 0 := by
      have hmem : y ∈ p.ker := by simpa [hpker] using hyN
      exact (LinearMap.mem_ker (f := p)).1 hmem
    have hq0 : q = 0 := by
      calc
        q = p (s q) := by rw [hs q]
        _ = p y := by rw [hq]
        _ = 0 := hpy
    calc
      y = s q := hq.symm
      _ = s 0 := by rw [hq0]
      _ = 0 := map_zero s
  -- Step 3 : assemble the basis.
  let v1 : ι → M := fun i => (bN i : M)
  let v2 : κ → M := fun k => s (bQ k)
  let w : ι ⊕ κ → M := Sum.elim v1 v2
  -- linear independence of the N-part (image of bN in M)
  have hli1 : LinearIndependent R v1 := by
    have h := LinearIndependent.map' (M' := M) bN.linearIndependent N.subtype (Submodule.ker_subtype N)
    simpa [v1, Function.comp_def] using h
  -- linear independence of the C-part (image of bQ under the section)
  have hli2 : LinearIndependent R v2 := by
    have hpv : p ∘ v2 = bQ := by
      funext k
      exact hs (bQ k)
    have hf : LinearIndependent R (p ∘ v2) := by
      simpa [hpv] using bQ.linearIndependent
    exact LinearIndependent.of_comp (v := v2) (f := p) hf
  -- disjointness of the spans
  have hspan1_le_N : Submodule.span R (Set.range v1) ≤ N := by
    rw [Submodule.span_le]
    intro y hy
    rcases hy with ⟨i, rfl⟩
    exact Submodule.coe_mem (bN i)
  have hspan2_le_C : Submodule.span R (Set.range v2) ≤ C := by
    rw [Submodule.span_le]
    intro y hy
    rcases hy with ⟨k, rfl⟩
    exact LinearMap.mem_range.mpr ⟨bQ k, rfl⟩
  have hdisjNC : Disjoint N C := by
    exact (disjoint_iff_inf_le.mpr (le_of_eq hinf))
  have hdisj_spans : Disjoint (Submodule.span R (Set.range v1))
      (Submodule.span R (Set.range v2)) := by
    exact Disjoint.mono hspan1_le_N hspan2_le_C hdisjNC
  have hliw : LinearIndependent R w := by
    have h := LinearIndependent.sum_type (v := v1) (v' := v2) hli1 hli2 hdisj_spans
    simpa [w] using h
  -- spanning
  have hN_le_span1 : N ≤ Submodule.span R (Set.range v1) := by
    intro u hu
    rw [Submodule.mem_span_range_iff_exists_fun]
    let z : N := ⟨u, hu⟩
    refine ⟨fun i : ι => (bN.repr z) i, ?_⟩
    have hzN : (∑ i : ι, (bN.repr z) i • bN i) = z := Module.Basis.sum_repr bN z
    have hA : N.subtype (∑ i : ι, (bN.repr z) i • bN i) =
        ∑ i : ι, (bN.repr z) i • (bN i : M) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul]
      rfl
    have hz : (∑ i : ι, (bN.repr z) i • (bN i : M)) = (z : M) := by
      calc
        (∑ i : ι, (bN.repr z) i • (bN i : M)) = N.subtype (∑ i : ι, (bN.repr z) i • bN i) := hA.symm
        _ = N.subtype z := congrArg N.subtype hzN
        _ = (z : M) := rfl
    simpa [v1] using hz
  have hspan1_le_spanW : Submodule.span R (Set.range v1) ≤ Submodule.span R (Set.range w) := by
    refine Submodule.span_mono ?_
    intro y hy
    rcases hy with ⟨i, rfl⟩
    exact ⟨Sum.inl i, by simp [w]⟩
  have hC_le_span2 : C ≤ Submodule.span R (Set.range v2) := by
    intro c hc
    rcases (LinearMap.mem_range.mp hc) with ⟨q, hq⟩
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun k : κ => (bQ.repr q) k, ?_⟩
    have hB : s (∑ k : κ, (bQ.repr q) k • bQ k) =
        ∑ k : κ, (bQ.repr q) k • (s (bQ k)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [map_smul]
    have hq2 : (∑ k : κ, (bQ.repr q) k • (s (bQ k))) = s q := by
      calc
        (∑ k : κ, (bQ.repr q) k • (s (bQ k))) = s (∑ k : κ, (bQ.repr q) k • bQ k) := hB.symm
        _ = s q := by rw [Module.Basis.sum_repr bQ q]
    simpa [v2, hq] using hq2
  have hspan2_le_spanW : Submodule.span R (Set.range v2) ≤ Submodule.span R (Set.range w) := by
    refine Submodule.span_mono ?_
    intro y hy
    rcases hy with ⟨k, rfl⟩
    exact ⟨Sum.inr k, by simp [w]⟩
  have hspan : ⊤ ≤ Submodule.span R (Set.range w) := by
    intro x _
    have hxsup : x ∈ N ⊔ C := by
      rw [hsup]
      trivial
    rcases (Submodule.mem_sup.mp hxsup) with ⟨a, ha, c, hc, hsum⟩
    have ha_span1 : a ∈ Submodule.span R (Set.range v1) := hN_le_span1 ha
    have hc_span2 : c ∈ Submodule.span R (Set.range v2) := hC_le_span2 hc
    have ha_w : a ∈ Submodule.span R (Set.range w) := hspan1_le_spanW ha_span1
    have hc_w : c ∈ Submodule.span R (Set.range w) := hspan2_le_spanW hc_span2
    have : a + c ∈ Submodule.span R (Set.range w) := Submodule.add_mem _ ha_w hc_w
    rwa [hsum] at this
  -- the basis of M
  let bM0 : Module.Basis (ι ⊕ κ) R M := Module.Basis.mk hliw hspan
  let φ : ι ⊕ κ ≃ Fin (Fintype.card (ι ⊕ κ)) := Fintype.equivFin (ι ⊕ κ)
  refine ⟨Fintype.card (ι ⊕ κ), bM0.reindex φ, ⟨fun i => φ (Sum.inl i), ?_⟩, ?_⟩
  · intro i₁ i₂ h
    exact Sum.inl_injective (Equiv.injective φ h)
  · intro i
    change (bN i : M) = (bM0.reindex φ) (φ (Sum.inl i))
    rw [Module.Basis.reindex_apply]
    simp [bM0, w, v1]

end Commons.LinearAlgebra.FreeModule