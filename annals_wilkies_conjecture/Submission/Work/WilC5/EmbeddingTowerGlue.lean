import Mathlib
import Submission.Work.WilC5.S4StepNewSetup

namespace Work.WilC5

open FirstOrder Language

/-- **Gluing a coherent tower of substructures and embeddings.**  If `T : ℕ → LRc.Substructure K`
is an increasing sequence of substructures and `σ n : ↥(T n) → L` are compatible `LRc`-embeddings
(`σ` on the smaller `T m` agrees with `σ` on the larger `T n`), then they glue to a single
`LRc`-embedding `σ'` of the substructure `S` whose carrier is the union `⋃ n, (T n : Set K)`,
agreeing with each `σ n` — provided `S` really is a substructure of `K` with that carrier (`hS`).
This is the "union of the tower" step of vdDMM Lemma 4.4.  The proof: an element of the union lies
in some `T n`; well-definedness and respect for the function symbols are by choosing an index above
the finitely many indices involved (using `hmono`), and `LRc` has no relation symbols. -/
theorem EmbeddingTowerGlue
    {K L : Type} [FirstOrder.Language.Structure WilkiesDesign.CG.LRc K]
      [FirstOrder.Language.Structure WilkiesDesign.CG.LRc L]
    (T : ℕ → WilkiesDesign.CG.LRc.Substructure K)
    (hmono : ∀ m n : ℕ, m ≤ n → T m ≤ T n)
    (σ : ∀ n : ℕ, WilkiesDesign.CG.LRc.Embedding ↥(T n) L)
    (hcoh : ∀ (m n : ℕ) (h : m ≤ n) (a : K) (hm : a ∈ (T m : Set K))
      (hn : a ∈ (T n : Set K)), σ n ⟨a, hn⟩ = σ m ⟨a, hm⟩)
    (S : WilkiesDesign.CG.LRc.Substructure K)
    (hS : (S : Set K) = ⋃ n, (T n : Set K)) :
    ∃ σ' : WilkiesDesign.CG.LRc.Embedding ↥S L,
      ∀ (n : ℕ) (a : K) (hn : a ∈ (T n : Set K)) (haS : a ∈ (S : Set K)),
        σ' ⟨a, haS⟩ = σ n ⟨a, hn⟩ := by
  classical
  -- Every element of `S` lies in some member of the tower.
  have hmemS : ∀ x : ↥S, ∃ n, (x : K) ∈ (T n : Set K) := by
    intro x
    have hx : (x : K) ∈ ⋃ n, (T n : Set K) := by rw [← hS]; exact x.2
    exact Set.mem_iUnion.mp hx
  -- Choose for every element an index containing it, and glue by evaluating there.
  let idx : ↥S → ℕ := fun x => Classical.choose (hmemS x)
  have idx_spec : ∀ x : ↥S, (x : K) ∈ (T (idx x) : Set K) := fun x =>
    Classical.choose_spec (hmemS x)
  let g : ↥S → L := fun x => (σ (idx x)) ⟨(x : K), idx_spec x⟩
  -- The glued map is computed by *any* index whose member contains the point.
  have hg_eq : ∀ (x : ↥S) (n : ℕ) (hn : (x : K) ∈ (T n : Set K)),
      g x = σ n ⟨(x : K), hn⟩ := by
    intro x n hn
    have hmk : (x : K) ∈ (T (max (idx x) n) : Set K) :=
      hmono _ _ (le_max_left _ _) (idx_spec x)
    have hnk : (x : K) ∈ (T (max (idx x) n) : Set K) :=
      hmono _ _ (le_max_right _ _) hn
    have h1 := hcoh (idx x) (max (idx x) n) (le_max_left _ _) (x : K) (idx_spec x) hmk
    have h2 := hcoh n (max (idx x) n) (le_max_right _ _) (x : K) hn hnk
    have h3 : σ (max (idx x) n) ⟨(x : K), hmk⟩ = σ (max (idx x) n) ⟨(x : K), hnk⟩ :=
      congrArg (σ (max (idx x) n)) (Subtype.ext rfl)
    have hgx : g x = σ (idx x) ⟨(x : K), idx_spec x⟩ := rfl
    rw [hgx, ← h1, h3, h2]
  -- Injectivity: two points with the same image lie in a common member, where an embedding acts.
  have hg_inj : Function.Injective g := by
    intro x y hxy
    have hxk : (x : K) ∈ (T (max (idx x) (idx y)) : Set K) :=
      hmono _ _ (le_max_left _ _) (idx_spec x)
    have hyk : (y : K) ∈ (T (max (idx x) (idx y)) : Set K) :=
      hmono _ _ (le_max_right _ _) (idx_spec y)
    rw [hg_eq x _ hxk, hg_eq y _ hyk] at hxy
    have h2 := (σ (max (idx x) (idx y))).injective hxy
    have h3 : (x : K) = (y : K) := by
      have := congrArg (fun t : ↥(T (max (idx x) (idx y))) => (t : K)) h2
      simpa using this
    exact Subtype.ext h3
  -- Compatibility with function symbols: choose one index above all the finitely many indices
  -- involved, where a single embedding computes everything.
  have hg_map_fun : ∀ {n : ℕ} (f : WilkiesDesign.CG.LRc.Functions n) (v : Fin n → ↥S),
      g (FirstOrder.Language.Structure.funMap f v) =
        FirstOrder.Language.Structure.funMap f (g ∘ v) := by
    intro n f v
    let N : ℕ := Finset.univ.sup (fun i : Fin n => idx (v i))
    have hvN : ∀ i, (v i : K) ∈ (T N : Set K) := fun i =>
      hmono _ _ (Finset.le_sup (f := fun i : Fin n => idx (v i)) (Finset.mem_univ i))
        (idx_spec (v i))
    let w : Fin n → ↥(T N) := fun i => ⟨(v i : K), hvN i⟩
    have hres : ((FirstOrder.Language.Structure.funMap f v : ↥S) : K) ∈ (T N : Set K) := by
      have hcv : ((FirstOrder.Language.Structure.funMap f v : ↥S) : K)
          = FirstOrder.Language.Structure.funMap f (fun i => ((v i : ↥S) : K)) := rfl
      rw [hcv]
      exact (T N).fun_mem f (fun i => ((v i : ↥S) : K)) hvN
    have harg : (⟨((FirstOrder.Language.Structure.funMap f v : ↥S) : K), hres⟩ : ↥(T N))
        = FirstOrder.Language.Structure.funMap f w := Subtype.ext rfl
    rw [hg_eq (FirstOrder.Language.Structure.funMap f v) N hres, harg,
      FirstOrder.Language.Embedding.map_fun (σ N) f w]
    congr 1
    funext i
    show σ N (w i) = g (v i)
    exact (hg_eq (v i) N (hvN i)).symm
  -- `LRc` has no relation symbols, so the relation clause is vacuous.
  have hg_map_rel : ∀ {n : ℕ} (r : WilkiesDesign.CG.LRc.Relations n) (v : Fin n → ↥S),
      FirstOrder.Language.Structure.RelMap r (g ∘ v) ↔
        FirstOrder.Language.Structure.RelMap r v := by
    intro n r v
    rcases r with (h | h) | h <;> exact h.elim
  refine ⟨{ toEmbedding := ⟨g, hg_inj⟩,
             map_fun' := fun {n} f v => hg_map_fun f v,
             map_rel' := fun {n} r v => hg_map_rel r v }, ?_⟩
  intro n a hn haS
  exact hg_eq ⟨a, haS⟩ n hn

end Work.WilC5
