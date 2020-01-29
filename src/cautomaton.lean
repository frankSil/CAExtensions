import grid utils data.vector

open utils

namespace grid

attribute [simp, reducible]
def Q (α : Type*) [grid α] := relative_grid.carrier α

end grid

open grid

section cautomatons

structure cautomaton (α : Type) [decidable_eq α] :=
  (g     : vec_grid₀ α)
  (empty : α)
  (neigh : point → list point)
  (bound : (bounding_box → bounding_box) ⊕ (α → vec_grid₀ α → point → α))
  (f     : α → list α → α)

end cautomatons

section cautomaton_instances

variables {α : Type} [decidable_eq α] [has_to_string α] (a : cautomaton α)

open grid

def cautomaton_to_str := grid_str a.g

instance : has_to_string (cautomaton α) := ⟨cautomaton_to_str⟩

instance : has_repr (cautomaton α) := ⟨cautomaton_to_str⟩

end cautomaton_instances

section cautomaton_quot_setoid_eq 

variables {α : Type} [decidable_eq α] (a a₁ a₂ a₃ : cautomaton α)

end cautomaton_quot_setoid_eq

namespace cautomaton

end cautomaton

namespace cautomatons

open cautomaton grid

def neumann : point → list point
  | ⟨x, y⟩ := 
  [            ⟨x, y - 1⟩,
   ⟨x - 1, y⟩,             ⟨x + 1, y⟩,
               ⟨x, y + 1⟩             ]

def moore : point → list point
  | ⟨x, y⟩ :=
  [ ⟨x - 1, y - 1⟩, ⟨x, y - 1⟩, ⟨x + 1, y - 1⟩,
    ⟨x - 1, y    ⟩,             ⟨x + 1, y    ⟩,
    ⟨x - 1, y + 1⟩, ⟨x, y + 1⟩, ⟨x + 1, y + 1⟩ ]


def bounded_neigh {α} [grid α] (g : α)
  (f : point → list point) (p : grid_point g) : list point := f p

instance neigh_gridpoint_coe {α} [grid α] (g : α) :
  has_coe (point → list point)
          (grid_point g → list point) := ⟨bounded_neigh g⟩

def ext_id : bounding_box → bounding_box := id

def ext_one (bb : bounding_box) : bounding_box :=
  ⟨⟨bb.1.1 - 1, bb.1.2 - 1⟩, ⟨bb.2.1 + 1, bb.2.2 + 1⟩,
  ⟨
    (add_lt_add (grid_bounded_iff.1 bb.h).1 dec_trivial),
    (add_lt_add (grid_bounded_iff.1 bb.h).2 dec_trivial)⟩
  ⟩

lemma rows_of_box_ext_one {bb} :
  rows_of_box (ext_one bb) = rows_of_box bb + 2 :=
begin
  cases bb with p₁ p₂ h,
  simp [ext_one, rows_of_box],
  rw ← int.coe_nat_eq_coe_nat_iff,
  rw int.coe_nat_add, simp,
  rw grid_bounded_iff at h, cases h,
  repeat { rw int.nat_abs_of_nonneg }; linarith
end

lemma cols_of_box_ext_one {bb} :
  cols_of_box (ext_one bb) = cols_of_box bb + 2 :=
begin
  cases bb with p₁ p₂ h,
  simp [ext_one, cols_of_box],
  rw ← int.coe_nat_eq_coe_nat_iff,
  rw int.coe_nat_add, simp,
  rw grid_bounded_iff at h, cases h,
  repeat { rw int.nat_abs_of_nonneg }; linarith
end

lemma bl_ext_one {bb} : (ext_one bb).p₁ = ⟨bb.p₁.x - 1, bb.p₁.y - 1⟩ := rfl

lemma tr_ext_one {bb} : (ext_one bb).p₂ = ⟨bb.p₂.x + 1, bb.p₂.y + 1⟩ := rfl

end cautomatons

section cautomaton_props

variables {α : Type} [decidable_eq α] (a : cautomaton α)

end cautomaton_props

section cautomaton_ops

open function list prod relative_grid

variables variables {α : Type} [decidable_eq α] (a : cautomaton α)

def asize := size a.g

def bbox_of_caut := grid_bounds a.g

theorem caut_eq_iff {a₁ a₂ : cautomaton α}
  (hempty : a₁.empty = a₂.empty)
  (hneigh : a₁.neigh = a₂.neigh)
  (hbound : a₁.bound = a₂.bound)
  (hf : a₁.f = a₂.f)
  (hext : a₁.bound = a₂.bound) : a₁ = a₂ ↔ a₁.g = a₂.g :=
  ⟨λh, by simp [h], λh, by cases a₁; cases a₂; congr; cc⟩

private lemma pres_nonempty {α β : Type} {f} {filtered : list (α × β)}
  {l : list ℤ}
  (h : ¬empty_list filtered) (h₁ : l = map f ((fst ∘ unzip) filtered)) : 
  ¬empty_list l :=
  by simp [h₁, map_empty_iff_l_empty, unzip_fst_empty_iff_l_empty, h]

def compute_bounds : bounding_box :=
  let bounded  := gip_g a.g in
  let mapped   := ℘ a.g in
  let zipped   := zip bounded mapped in
  let filtered := filter (λx, snd x ≠ a.empty) zipped in
  if h : empty_list filtered
  then ⟨gbl a.g, gtr a.g, grid_is_bounding_box⟩ else
  let unzipped := fst ∘ unzip $ filtered in
  let xs       := map point.x unzipped in
  let ys       := map point.y unzipped in
  let min_x    := min_element xs (pres_nonempty h $ by simp) in
  let max_x    := max_element xs (pres_nonempty h $ by simp) in
  let min_y    := min_element ys (pres_nonempty h $ by simp) in 
  let max_y    := max_element ys (pres_nonempty h $ by simp) in
  ⟨⟨min_x, min_y⟩, ⟨max_x + 1, max_y + 1⟩,
  begin
    simp [(↗), min_x, max_x, min_y, max_y];
    split; rw add_comm; exact int.lt_add_one_of_le (min_elem_le_max_elem _ _)
  end⟩

lemma compute_bounds_pres_overlaid
  : overlaid_by (compute_bounds a) ⟨gbl a.g, gtr a.g, grid_is_bounding_box⟩
  :=
begin
  simp [overlaid_by, compute_bounds],
  generalize h₂ : gip_g a.g = indices,
  by_cases h : empty_list (filter (λ (x : point × α), x.snd ≠ a.empty)
                                  (zip indices ℘ (a.g))); simp [h₂, h],
  {exact ⟨⟨le_refl _, le_refl _⟩, ⟨le_refl _, le_refl _⟩⟩},
  {
    split; split,
    {
      apply le_min_elem_of_all _ _ _ (λx, λh₁, _),
      simp at h₁, rcases h₁ with ⟨y₁, rest, h₃⟩, subst h₃,
      apply (zunzip_filter_first_irrel rest),
      rw ← h₂, intros y h₄,
      have h₅ := gip_g_in_grid h₄,
      simp [flip, is_in_grid, grid_bounds] at h₅,
      exact h₅.2.1
    },    
    { 
      rw [add_comm, ← sub_le_sub_iff_right (1 : ℤ), add_sub_assoc],
      have : 1 - 1 = (0 : ℤ), from dec_trivial, rw this, rw add_zero,
      apply max_le_elem_of_all _ _ _ (λx, λh₁, _),
      simp at h₁, rcases h₁ with ⟨y₁, rest, h₃⟩, subst h₃,
      apply (zunzip_filter_first_irrel rest), rw ← h₂, intros y h₄,
      have h₅ := gip_g_in_grid h₄,
      simp [flip, is_in_grid, grid_bounds] at h₅,
      simp [gtr],
      rw [add_comm (-1 : ℤ), ← sub_eq_add_neg, int.le_sub_one_iff],
      exact h₅.2.2
    },
    {
      rw [add_comm, ← sub_le_sub_iff_right (1 : ℤ), add_sub_assoc],
      have : 1 - 1 = (0 : ℤ), from dec_trivial, rw [this, add_zero],
      apply max_le_elem_of_all _ _ _ (λx, λh₁, _),
      simp at h₁, rcases h₁ with ⟨y₁, rest, h₃⟩, subst h₃,
      apply (zunzip_filter_first_irrel rest),
      rw ← h₂, intros y h₄,
      have h₅ := gip_g_in_grid h₄,
      simp [flip, is_in_grid, grid_bounds] at h₅,
      rw int.le_sub_one_iff,
      exact h₅.1.2
    }, 
    {
      apply le_min_elem_of_all _ _ _ (λx, λh₁, _),
      simp at h₁, rcases h₁ with ⟨y₁, rest, h₃⟩, subst h₃,
      simp [expand_gtr, point.x, point.y],
      apply (zunzip_filter_first_irrel rest),
      rw ← h₂, intros y h₄,
      have h₅ := gip_g_in_grid h₄,
      simp [flip, is_in_grid, grid_bounds, expand_gtr, point.x] at h₅,
      rcases h₅ with ⟨⟨h₅, h₆⟩, ⟨h₇, h₈⟩⟩,
      linarith
    }
  }
end

lemma compute_bounds_pres_grid :
    uncurry (↗) (points_of_box $ compute_bounds a) :=
begin
  generalize h : compute_bounds a = bounds,
  simp [points_of_box, uncurry, bounds.h]
end

lemma in_nth_of_zip  {e₁ : point} {e₂} :
  (e₁, e₂) ∈ zip (gip_g a.g) ℘(a.g) →
    (∀{H₁} {H₂}, e₂ = abs_data a.g ⟨⟨e₁.y, H₁⟩, ⟨e₁.x, H₂⟩⟩) :=
begin
  intros H₀ H₁ H₂,
  rw mem_iff_nth_le at H₀,
  cases H₀ with i H₀r, cases H₀r with H₀r₁ H₀r₂,
  symmetry' at H₀r₂,
  have leneq : length (gip_g a.g) = length ℘(a.g),
    by simp [length_gip_g, length_generate_eq_size],
  have len₁ : i < length ℘(a.g),
    { rw [length_zip, leneq, min_self] at H₀r₁, exact H₀r₁ },
  have len₂ : i < length (gip_g a.g),
    { rw [length_zip, ← leneq, min_self] at H₀r₁, exact H₀r₁ }, 
  have eq : nth_le (gip_g (a.g)) i len₂ = e₁ ∧
            nth_le ℘(a.g) i len₁ = e₂, from nth_le_zip' H₀r₂,
  cases eq with eq₁ eq₂, rw ← eq₂,
  rw nth_generate, rw nth_le_gip_g at eq₁,
  congr, rw ← eq₁, rw ← eq₁
end

lemma in_zip_dep {p} {e} {i} {hi}
  (h : (p, e) = nth_le (zip (gip_g a.g) ℘(a.g)) i hi) :
  nth_le (gip_g (a.g)) i 
    begin
      have leneq : length (gip_g a.g) = length (℘(a.g)),
        by simp [length_gip_g, length_generate_eq_size],
      rw [length_zip, leneq, min_self] at hi,
      simpa [leneq]
    end = p ∧ nth_le ℘(a.g) i
    begin
      have leneq : length (gip_g a.g) = length (℘(a.g)),
        by simp [length_gip_g, length_generate_eq_size],
      rw [length_zip, leneq, min_self] at hi,
      simpa [leneq]
    end = e ∧
  i = |p.y - a.g.o.y| * a.g.c + |p.x - a.g.o.x| :=
begin
  have : nth_le (gip_g (a.g)) i
    begin
      have leneq : length (gip_g a.g) = length (℘(a.g)),
        by simp [length_gip_g, length_generate_eq_size],
      rw [length_zip, leneq, min_self] at hi,
      simpa [leneq]
    end = p ∧ nth_le ℘(a.g) i 
    begin
      have leneq : length (gip_g a.g) = length (℘(a.g)),
        by simp [length_gip_g, length_generate_eq_size],
      rw [length_zip, leneq, min_self] at hi,
      simpa [leneq]
    end = e,
    from nth_le_zip' h,
  have ieq : i = |p.y - a.g.o.y| * a.g.c + |p.x - a.g.o.x|,
    {
      have leneq : length (gip_g a.g) = length (℘(a.g)),
        by simp [length_gip_g, length_generate_eq_size],
      cases this with h₁ h₂, clear h₂, clear h,
      rw [length_zip, leneq, min_self] at hi, rw ← leneq at hi, clear leneq,
      rw nth_le_gip_g at h₁, rw length_gip_g at hi,
      rw ← h₁,
      simp [bl, cols], rw mod_add_div_coe
    },
  exact ⟨this.1, this.2, ieq⟩
end

lemma nth_le_gen_iff_abs_data_gip {i} {H} {H₁} {e} :
  nth_le ℘(a.g) i H = e ↔
  abs_data a.g ⟨
    ⟨(nth_le (gip_g a.g) i H₁).y,
      begin
        simp [nth_le_gip_g], split,
          {norm_cast, linarith},
          {
            apply add_lt_of_lt_sub_left,
            simp [expand_gtr, bl],
            rw length_generate_eq_size at H, unfold size at H,
            norm_cast,
            rw nat.div_lt_iff_lt_mul _ _,
            exact H,
            have := a.g.h, simp [cols],
            apply pos_of_mul_pos_left this,
            apply zero_le _
          }
      end⟩,
    ⟨(nth_le (gip_g a.g) i H₁).x,
      begin
        simp [nth_le_gip_g], split,
          {norm_cast},
          {
            apply add_lt_of_lt_sub_left,
            simp [expand_gtr, bl],
            apply int.mod_lt_of_pos,
            have := a.g.h, simp [cols],
            apply pos_of_mul_pos_left this,
            apply zero_le _
          }
      end⟩
  ⟩ = e :=
begin
  split; intros h,
    {rw nth_generate at h, rw ← h, simp [nth_le_gip_g]},
    {rw nth_generate, rw ← h, simp [nth_le_gip_g]}
end

lemma mem_zip_gip_gen {p} {elem} 
  (h : p ∈ a.g)
  (h₁ : elem = abs_data (a.g) {x := ⟨p.x, h.2⟩, y := ⟨p.y, h.1⟩}) :
  (p, elem) ∈ zip (gip_g (a.g)) ℘(a.g) :=
begin
  rw mem_iff_nth_le,
  let i := |p.x - ((a.g).o).x| + |p.y - ((a.g).o).y| * ((a.g).to_vec_grid).c,
  have H : i < size a.g,
    {
      simp [i, size, rows, cols, -sub_eq_add_neg], rw add_comm,
      apply linearize_array,
        {
          rcases h with ⟨⟨a₁, a₂⟩, ⟨a₃, a₄⟩⟩, 
          simp [expand_gtr, gbl, bl, rows, cols] at a₁ a₂ a₃ a₄,
          rw ← int.coe_nat_lt_coe_nat_iff,
          rw int.nat_abs_of_nonneg; try { assumption },
          linarith, linarith
        },
        {
          rcases h with ⟨⟨a₁, a₂⟩, ⟨a₃, a₄⟩⟩, 
          simp [expand_gtr, gbl, bl, rows, cols] at a₁ a₂ a₃ a₄,
          rw ← int.coe_nat_lt_coe_nat_iff,
          rw int.nat_abs_of_nonneg; try { assumption },
          linarith, linarith
        }
    },
  have leneq : length (gip_g a.g) = length ℘(a.g),
    by simp [length_gip_g, length_generate_eq_size],
  have H₀ : i < length (gip_g a.g),
    by rw length_gip_g; exact H,
  have H₁ : i < length (zip (gip_g a.g) ℘(a.g)),
    by rwa [length_zip, leneq, min_self, length_generate_eq_size],
  use i, use H₁, symmetry,
  rcases h with ⟨⟨a₁, a₂⟩, ⟨a₃, a₄⟩⟩, 
  simp [expand_gtr, gbl, bl, rows, cols] at a₁ a₂ a₃ a₄,
  apply nth_le_zip,
  rw nth_le_gip_g, cases p, simp, split, ring,
  apply add_eq_of_eq_sub', simp [expand_gtr, bl, cols],
  repeat { rw int.nat_abs_of_nonneg; try { linarith } },
  apply int.mod_eq_of_lt; try { linarith },
  apply add_eq_of_eq_sub', simp [cols, bl], rw ← add_assoc, 
  rw int.add_mul_div_right,
  rw int.div_eq_zero_of_lt; linarith,
  simp, intros contra, let falso := a.g.h,
  rw contra at falso, linarith,
  rw h₁, rw nth_generate, congr,
  simp [i],
  apply add_eq_of_eq_sub', simp [expand_gtr, bl, cols],
  rw int.add_mul_div_right,
  rw int.div_eq_zero_of_lt, rw int.nat_abs_of_nonneg; linarith,
  rw int.nat_abs_of_nonneg; linarith,
  rw int.nat_abs_of_nonneg; linarith,
  intros contra, let falso := a.g.h, simp at contra,
  rw contra at falso, linarith,
  simp [i],
  apply add_eq_of_eq_sub', simp [expand_gtr, bl, cols],
  repeat { rw int.nat_abs_of_nonneg; try { linarith } },
  apply int.mod_eq_of_lt; try { linarith }, exact H₀,
  rw ← leneq, exact H₀
end

lemma y_notin_elem_empty {x} {y} {H₁} {H₂}
  (notin : x ∉ map point.x
         ((unzip (filter (λ (x : point × α), ¬x.snd = a.empty)
         (zip (gip_g (a.g)) ℘(a.g)))).fst)) :
  abs_data (a.g) {x := ⟨x, H₁⟩, y := ⟨y, H₂⟩} = a.empty :=
begin
  let p : point := ⟨x, y⟩,
  have eqp : p = ⟨x, y⟩, from rfl,
  have eq₁ : p ∈ gip_g a.g,
    {apply in_gip_g_of_in_g, exact ⟨H₂, H₁⟩},
  rw [mem_map, not_exists] at notin,
  let elem := abs_data a.g ⟨⟨p.y, H₂⟩, ⟨p.x, H₁⟩⟩,
  have eqelem : elem = abs_data a.g ⟨⟨p.y, H₂⟩, ⟨p.x, H₁⟩⟩, from rfl,
  specialize notin p, simp at notin,
  by_contradiction contra,
  have eq₂ : (p, elem) ∈
    filter (λ (x : point × α), ¬x.snd = a.empty) (zip (gip_g a.g) ℘(a.g)),
    {
      rw @mem_filter _ (λ (x : point × α), ¬x.snd = a.empty),
      simp, split, swap 2, rw eqelem, refine contra, 
      apply mem_zip_gip_gen _ (in_grid_iff_in_gip_g.2 eq₁) eqelem
    },
  have eq₃ : p ∈ (unzip (filter (λ (x : point × α), ¬x.snd = a.empty)
                          (zip (gip_g (a.g)) ℘(a.g)))).fst,
    {rw in_unzip_iff, use elem, exact eq₂},
  contradiction
end

lemma x_notin_elem_empty {y} {x} {H₁} {H₂}
  (notin : y ∉ map point.y
         ((unzip (filter (λ (x : point × α), ¬x.snd = a.empty)
         (zip (gip_g (a.g)) ℘(a.g)))).fst)) :
  abs_data (a.g) {x := ⟨x, H₁⟩, y := ⟨y, H₂⟩} = a.empty :=
begin
  let p : point := ⟨x, y⟩,
  have eqp : p = ⟨x, y⟩, from rfl,
  have eq₁ : p ∈ gip_g a.g,
    {apply in_gip_g_of_in_g, exact ⟨H₂, H₁⟩},
  rw [mem_map, not_exists] at notin,
  let elem := abs_data a.g ⟨⟨p.y, H₂⟩, ⟨p.x, H₁⟩⟩,
  have eqelem : elem = abs_data a.g ⟨⟨p.y, H₂⟩, ⟨p.x, H₁⟩⟩, from rfl,
  specialize notin p, simp at notin,
  by_contradiction contra,
  have eq₂ : (p, elem) ∈
    filter (λ (x : point × α), ¬x.snd = a.empty) (zip (gip_g a.g) ℘(a.g)),
    {
      rw @mem_filter _ (λ (x : point × α), ¬x.snd = a.empty),
      simp, split, swap 2, rw eqelem, refine contra, 
      apply mem_zip_gip_gen _ (in_grid_iff_in_gip_g.2 eq₁) eqelem
    },
  have eq₃ : p ∈ (unzip (filter (λ (x : point × α), ¬x.snd = a.empty)
                          (zip (gip_g (a.g)) ℘(a.g)))).fst,
    {rw in_unzip_iff, use elem, exact eq₂},
  contradiction
end

lemma y_lt_min_elem_empty {x} {H₁} {H₂}
  (h : x < min_element (map point.x
             ((unzip (filter (λ (x : point × α), ¬x.snd = a.empty)
                        (zip (gip_g (a.g)) ℘(a.g)))).fst)) H₁) :
  ∀y {H₃}, abs_data (a.g) {x := ⟨x, H₂⟩, y := ⟨y, H₃⟩} = a.empty :=
begin
  intros,
  have notin : x ∉ map point.x
               ((unzip (filter (λ (x : point × α), ¬x.snd = a.empty)
                          (zip (gip_g (a.g)) ℘(a.g)))).fst),
    from not_mem_of_lt_min_element H₁ h,
  apply y_notin_elem_empty _ notin
end

lemma add_one_y_gt_max_elem_empty {x} {H₁} {H₂}
  (h : 1 + max_element (map point.x
             ((unzip (filter (λ (x : point × α), ¬x.snd = a.empty)
                        (zip (gip_g (a.g)) ℘(a.g)))).fst)) H₁ ≤ x) :
  ∀y {H₃}, abs_data (a.g) {x := ⟨x, H₂⟩, y := ⟨y, H₃⟩} = a.empty :=
begin
  intros,
  have notin : x ∉ (map point.x
             ((unzip (filter (λ (x : point × α), ¬x.snd = a.empty)
                        (zip (gip_g (a.g)) ℘(a.g)))).fst)),
    from not_mem_of_add_one_max_elem_gt _ h,
  apply y_notin_elem_empty _ notin
end

lemma x_lt_min_elem_empty {y} {H₁} {H₂}
  (h : y < min_element (map point.y
             ((unzip (filter (λ (x : point × α), ¬x.snd = a.empty)
                        (zip (gip_g (a.g)) ℘(a.g)))).fst)) H₁) :
  ∀x {H₃}, abs_data (a.g) {x := ⟨x, H₃⟩, y := ⟨y, H₂⟩} = a.empty :=
begin
  intros,
  have notin : y ∉ map point.y
             ((unzip (filter (λ (x : point × α), ¬x.snd = a.empty)
                        (zip (gip_g (a.g)) ℘(a.g)))).fst),
    from not_mem_of_lt_min_element _ h,
  apply x_notin_elem_empty _ notin
end

lemma add_one_x_lt_max_elem_empty {y} {H₁} {H₂}
  (h : 1 + max_element (map point.y
             ((unzip (filter (λ (x : point × α), ¬x.snd = a.empty)
                        (zip (gip_g (a.g)) ℘(a.g)))).fst)) H₁ ≤ y) :
  ∀x {H₃}, abs_data (a.g) {x := ⟨x, H₃⟩, y := ⟨y, H₂⟩} = a.empty :=
begin
  intros,
  have notin : y ∉ map point.y
             ((unzip (filter (λ (x : point × α), ¬x.snd = a.empty)
                        (zip (gip_g (a.g)) ℘(a.g)))).fst),
    from not_mem_of_add_one_max_elem_gt _ h,
  apply x_notin_elem_empty _ notin
end

lemma empty_of_mem_gip_nmem_compute {p : point}
  (h : p ∈ a.g)
  (h₁ : p ∉ compute_bounds a) :
  abs_data (a.g) {x := ⟨p.x, h.2⟩, y := ⟨p.y, h.1⟩} = a.empty :=
begin
  unfold compute_bounds at h₁,
  simp [flip, is_in_grid, is_in_grid', is_bounded] at h,
  rcases h with ⟨⟨B₁, B₂⟩, ⟨B₃, B₄⟩⟩,
  simp [expand_gtr, bl, cols, rows] at B₁ B₂ B₃ B₄,
  let i := |p.y - a.g.o.y| * a.g.c + |p.x - a.g.o.x|,
  have A₁ : p.y - a.g.o.y ≥ 0, by linarith,
  have A₂ : p.x - a.g.o.x ≥ 0, by linarith,
  have A₃ : i < size a.g,
    {
      simp [i, size, rows, cols, -sub_eq_add_neg, -add_comm],
      apply linearize_array,
        {
          rw ← int.coe_nat_lt_coe_nat_iff,
          rw int.nat_abs_of_nonneg; try { assumption },
          linarith
        },
        {
          rw ← int.coe_nat_lt_coe_nat_iff,
          rw int.nat_abs_of_nonneg; try { assumption },
          linarith
        }
    },
  have A₄ : 0 ≤ i, by linarith,
  cases p with x y,
  have eq₁ : (bl (a.g)).x + ↑|↑i| % ↑(cols (a.g)) = x,
    {
      simp, norm_cast, simp [-sub_eq_add_neg, bl],
      simp only [cols],
      repeat { rw int.nat_abs_of_nonneg; try { assumption } },
      ring, simp [-sub_eq_add_neg] at *,
      rw add_eq_of_eq_neg_add, simp, 
      rw ← sub_eq_add_neg,
      rw int.mod_eq_of_lt,
      linarith,
      linarith
    },
  have eq₂ : (bl (a.g)).y + ↑|↑i| / ↑(cols (a.g)) = y,
    {
      simp, norm_cast, simp [-sub_eq_add_neg, bl],
      simp only [cols],
      repeat { rw int.nat_abs_of_nonneg; try { assumption } },
      ring, simp [-sub_eq_add_neg] at *,
      rw add_eq_of_eq_neg_add, simp, 
      rw ← sub_eq_add_neg,
      rw ← add_assoc, ring,
      rw int.add_mul_div_right,
      rw int.div_eq_zero_of_lt,
      simp,
      linarith,
      linarith,
      linarith
    },
  by_cases eq :
    empty_list (filter (λ (x : point × α), x.snd ≠ a.empty)
                       (zip (gip_g (a.g)) ℘(a.g))),
      {
        unfold empty_list at eq, symmetry' at eq,
        rw filter_eq_nil at eq, simp at eq,
        apply eq ⟨x, y⟩,
        simp [flip, is_in_grid, is_in_grid', is_bounded] at h,
        refine @nth_le_in_grid _ (int.nat_abs i) _ _ _ _,
        rw length_zip,
        rw length_gip_g, rw length_generate_eq_size, unfold size,
        rw min_eq_right, exact A₃, exact le_refl _,
        rw nth_le_zip, rw nth_le_gip_g,
          {congr, exact eq₁, exact eq₂},
          {
            rw nth_generate, congr, 
            exact eq₂, exact eq₁
          },
        rw length_gip_g, exact A₃,
        rw length_generate_eq_size, exact A₃
      },
      {
        simp [eq, flip, is_in_grid, is_bounded, -not_and] at h₁,
        rw not_and_distrib at h₁, cases h₁, rw not_and_distrib at h₁,
        cases h₁,
          {
            simp only [point.x, point.y] at *,
            rw not_le at h₁,
            apply x_lt_min_elem_empty _ h₁
          }, 
          {
            rw not_lt at h₁,
            apply add_one_x_lt_max_elem_empty _ h₁
          },
        rw not_and_distrib at h₁, cases h₁,
          {
            rw not_le at h₁,
            apply y_lt_min_elem_empty _ h₁
          },
          {
            rw not_lt at h₁,
            apply add_one_y_gt_max_elem_empty _ h₁
          }
      }
end

lemma exists_p_of_in_generate {x} (h : x ∈ ℘(a.g)) :
  ∃(p : point) (H : p ∈ gip_g a.g),
    abs_data a.g ⟨
      ⟨p.y, begin rw ← in_grid_iff_in_gip_g at H, exact H.1 end⟩,
      ⟨p.x, begin rw ← in_grid_iff_in_gip_g at H, exact H.2 end⟩
    ⟩ = x :=
begin
  rw mem_iff_nth_le at h,
  rcases h with ⟨i, ⟨h₁, h₂⟩⟩, 
  have : i < length (gip_g (a.g)),
    {rw length_gip_g, rw length_generate_eq_size at h₁, exact h₁},
  let p := nth_le (gip_g a.g) i this,
  have eqp : p = nth_le (gip_g (a.g)) i this, from rfl, 
  use p, intros,
  rw ← h₂,
  rw nth_generate, simp [nth_le_gip_g, bl, cols, eqp],
  have : p ∈ gip_g (a.g), { rw eqp, apply nth_le_mem },
  use this, congr
end

def canonical_grid :=
  compute_bounds a = ⟨gbl a.g, gtr a.g, grid_is_bounding_box⟩

def make_canonical : cautomaton α :=
  {a with g := ↑(subgrid a.g (compute_bounds a) (compute_bounds_pres_overlaid _))}

def is_canonical := make_canonical a = a

def aut_eq (a₁ a₂ : cautomaton α) : Prop :=
  (band : bool → bool → bool) (℘(make_canonical a₁).g = ℘(make_canonical a₂).g)
  $ (band : bool → bool → bool)
    ((make_canonical a₁).g.r = (make_canonical a₂).g.r)
    ((make_canonical a₁).g.c = (make_canonical a₂).g.c)

infix ` ~ₐ `:100 := aut_eq

instance decidable_aut_eq {α} [decidable_eq α] {a₁ a₂} :
  decidable (@aut_eq α _ a₁ a₂) := by simp [(~ₐ)]; apply_instance

def ext_aut (a : cautomaton α) : cautomaton α :=
  match a.bound with
    | (sum.inr _) := a
    | (sum.inl ext) :=
    let new_bb := ext (grid_bounds a.g) in
    let new_grid :=
      fgrid₀.mk
        (rows_of_box new_bb)
        (cols_of_box new_bb)
        (mul_pos rows_of_box_pos cols_of_box_pos)
        new_bb.p₁
        (λx y, if h : (⟨y, x⟩ : point) ∈ a.g
               then abs_data a.g $ grid_point_of_prod'
                       ((make_bounded h.1), (make_bounded h.2))
               else a.empty) in
    ⟨new_grid, a.empty, a.neigh, a.bound, a.f⟩
  end

def default_if_nex {α : Type*} [grid α] (empty : carrier α)
  (g : α) (p : point) : carrier α :=
  if h : p ∈ g
  then abs_data g (grid_point_of_prod' (in_grid_bounded g p h))
  else empty

section boundary

private lemma bound_periodic_modulo'
  {a} {b : ℤ} {c} (h : a > 0) :
  b ≤ (b + a) - 1 - (b - c - 1) % a :=
begin
  simp, repeat { rw ← sub_eq_add_neg },
  rw [
    ← add_sub_assoc, ← sub_eq_add_neg,
    ← le_add_iff_nonneg_left (1 : ℤ)
  ],
  change (1 : ℤ) with (0 + 1),
  rw int.add_one_le_iff, simp [-sub_eq_add_neg],
  rw ← add_sub_assoc, simp,
  apply lt_add_of_neg_add_lt, simp,
  apply int.mod_lt_of_pos,
  simpa [h]
end

private lemma bound_periodic_modulo''
  {a} {b : ℤ} {c} (h : a > 0) :
  (b + a) - 1 - (b - c - 1) % a < b + a :=
begin
  simp, rw ← add_assoc, repeat { rw ← sub_eq_add_neg },
  rw neg_lt,
  apply int.lt_of_add_one_le, simp [-sub_eq_add_neg],
  apply int.mod_nonneg,
  simp, linarith
end

def bound_periodic {α : Type*} [grid α] (empty : carrier α)
  (g : α) (p : point) : carrier α :=
  if h : p ∈ g
  then abs_data g (grid_point_of_prod' (in_grid_bounded g p h))
  else
    if b₁ : is_bounded (gbl g).y (gtr g).y p.y 
    then
      if p₁ : p.x ≥ (gtr g).x
      then abs_data g ⟨
        make_bounded b₁,
        ⟨(gbl g).x + (p.x - (gbl g).x) % cols g,
         begin
           split,
             {
               have : cols g > 0, from cols_pos,
               apply le_add_of_nonneg_right (int.mod_nonneg _ _),
               linarith
             },
             {simp [expand_gtr, int.mod_lt_of_pos, cols_pos]}
         end
        ⟩
      ⟩
      else abs_data g ⟨
        make_bounded b₁,
        ⟨(gtr g).x - 1 - ((gbl g).x - p.x - 1) % cols g,
         have h₂ : p.x < (gbl g).x,
           {
             by_cases p₃ : (gbl g).x ≤ p.x,
               {
                 have contra : is_bounded (gbl g).x (gtr g).x p.x,
                   from ⟨p₃, lt_of_not_ge p₁⟩,
                 simp only [(∉), flip, is_in_grid'] at h,
                 finish
               },
             {linarith}
           },
          ⟨
            bound_periodic_modulo' cols_pos,
            bound_periodic_modulo'' cols_pos
          ⟩
        ⟩
      ⟩
    else
    if b₂ : is_bounded (gbl g).x (gtr g).x p.x
    then
      if p₂ : p.y ≥ (gtr g).y
      then abs_data g ⟨
        ⟨(gbl g).y + (p.y - (gbl g).y) % rows g,
          ⟨
            begin
              simp only [gbl, le_add_iff_nonneg_right, sub_eq_add_neg],
              rw ← sub_eq_add_neg,
              apply int.mod_nonneg, simp,
              have : 0 < rows g, from rows_pos,
              linarith
            end,
            by simp [expand_gtr, int.mod_lt_of_pos, rows_pos]
          ⟩
        ⟩,
        make_bounded b₂
      ⟩
      else abs_data g ⟨
        ⟨(gtr g).y - 1 - ((gbl g).y - p.y - 1) % rows g,
          have h₂ : p.y < (gbl g).y,
            {
              replace p₂ := lt_of_not_ge p₂,
              by_cases p₃ : (gbl g).y ≤ p.y,
                {
                  have contra : is_bounded (gbl g).y (gtr g).y p.y,
                    from ⟨p₃, p₂⟩,
                  contradiction
                },
                {linarith}
            },
          ⟨
            bound_periodic_modulo' rows_pos,
            bound_periodic_modulo'' rows_pos
          ⟩
        ⟩,
        make_bounded b₂
      ⟩
    else empty

def bound_const {α : Type*} [grid α]
  (const : carrier α) (g : α) (p : point) : carrier α := default_if_nex const g p

end boundary

def next_gen (a : cautomaton α) : cautomaton α :=
  let new_grid := (ext_aut a).g in
  let cells := ℘ new_grid in
  let neighs := map a.neigh (gip_g new_grid) in
  let defaulted := 
    match a.bound with
      | (sum.inr boundf) := boundf a.empty new_grid
      | _ := @bound_const (vec_grid₀ α) _ a.empty new_grid
    end in
  let neigh_cells := map (list.map defaulted) neighs in
  let new_cells := zip_with a.f cells neigh_cells in
  let grid :=
    @vec_grid₀.mk _
      ⟨grid_rows new_grid, grid_cols new_grid,
       mul_pos rows_pos cols_pos,
      ⟨new_cells, by simp [
                       zip_with_len_l,
                       length_generate_eq_size,
                       size,
                       rows_eq_try_sub_bly,
                       cols_eq_trx_sub_blx,
                       length_gip_g,
                       length_gip,
                       grid_is_bounding_box
                     ]
                  ⟩⟩ new_grid.o in
    let next_config := (⟨grid, a.empty, a.neigh, a.bound, a.f⟩ : cautomaton α) in
    match a.bound with
      | (sum.inl _) := make_canonical next_config
      | _ := next_config
    end

attribute [simp]
lemma next_gen_empty : (next_gen a).empty = a.empty :=
  by cases a with _ _ _ bound _; cases bound; refl

attribute [simp]
lemma next_gen_neigh : (next_gen a).neigh = a.neigh :=
  by cases a with _ _ _ bound _; cases bound; refl

attribute [simp]
lemma next_gen_f : (next_gen a).f = a.f :=
  by cases a with _ _ _ bound _; cases bound; refl

attribute [simp]
lemma next_gen_ext : (next_gen a).bound = a.bound :=
  by cases a with _ _ _ bound _; cases bound; refl

attribute [simp]
lemma iterate_next_gen_empty {n} : (iterate next_gen a n).empty = a.empty :=
  by induction n with n ih; simp [iterate_zero, *, iterate_one]

attribute [simp]
lemma iterate_next_gen_neigh {n} : (iterate next_gen a n).neigh = a.neigh :=
  by induction n with n ih; simp [iterate_zero, *, iterate_one]

attribute [simp]
lemma iterate_next_gen_f {n} : (iterate next_gen a n).f = a.f :=
  by induction n with n ih; simp [iterate_zero, *, iterate_one]

attribute [simp]
lemma iterate_next_gen_ext {n} : (iterate next_gen a n).bound = a.bound :=
  by induction n with n ih; simp [iterate_zero, *, iterate_one]

def step_n (n : ℕ) := iterate next_gen a n

def periodic := {n // n ≠ 0 ∧ step_n a n = a}

def count_at_single {α : Type} [decidable_eq α] (neigh : list α) (valid : α) :=
  list.sum ∘ map (λc, if c = valid then 1 else 0) $ neigh

def yield_at_if_in_neigh {α : Type} [decidable_eq α]
  (a : cautomaton α) (p : point) :=
  if p ∈ a.neigh p
  then some $ @default_if_nex (vec_grid₀ α) _ a.empty a.g p
  else none

lemma step_n_zero : step_n a 0 = a := rfl

lemma step_n_succ {n} : step_n a (nat.succ n) = next_gen (step_n a n) := rfl

def yield_at (p : point) : α := @default_if_nex (vec_grid₀ α) _ a.empty a.g p

def mod_at (p : point) (x : α) (a : cautomaton α) : cautomaton α :=
  ⟨modify_at p x a.g, a.empty, a.neigh, a.bound, a.f⟩

def mod_many (l : list (point × α)) (a : cautomaton α) : cautomaton α :=
  ⟨modify_many l a.g, a.empty, a.neigh, a.bound, a.f⟩

end cautomaton_ops

section counting

variables {α : Type} [decidable_eq α] (a : cautomaton α)

def count (c : α) : ℕ := count_grid a.g c

lemma count_grid_eq_count {x} : count a x = count_grid a.g x := rfl

lemma count_cast_foa (a : vec_grid₀ α) {x} : count_grid ↑a x = count_grid a x :=
  by unfold_coes; simp [count_grid, gen_aof_eq_gen, gen_foa_eq_gen]

lemma count_cast_aof (a : fgrid₀ α) {x} : count_grid ↑a x = count_grid a x :=
  by unfold_coes; simp [count_grid, gen_aof_eq_gen, gen_foa_eq_gen]

lemma yield_at_nonempty {p} {a : cautomaton α}
  (h : yield_at a p ≠ a.empty) : p ∈ a.g :=
begin
  by_contradiction contra,
  unfold yield_at default_if_nex at h,
  rw dif_neg contra at h,
  contradiction
end

lemma count_uneq_in_subgrid' {a : cautomaton α} {x} (h : x ≠ a.empty) :
  list.count x (subgrid' (a.g) (compute_bounds a) (compute_bounds_pres_overlaid _)) =
  0 :=
begin
  unfold subgrid' list.count,
  rw list.countp_eq_length_filter,
  unfold list.attach,
  rw list.map_pmap,
  rw list.length_eq_zero,
  rw list.filter_eq_nil,
  intros cell H,
  rw list.mem_pmap at H,
  cases H with p rest, cases rest with h₁ h₂,
  have : (abs_data (a.g) ∘ inject_filter_bounded (a.g)) ⟨p, h₁⟩ = a.empty,
    {
      rw list.mem_filter at h₁,
      cases h₁ with h₂ h₃,
      simp [(∘), inject_filter_bounded, grid_point_of_mem, make_bounded],
      apply empty_of_mem_gip_nmem_compute,
      rw in_grid_iff_in_gip_g, exact h₂,
      exact h₃
    },
  cc
end

lemma count_nonempty_compute_bounds {a : cautomaton α} {x} (h : x ≠ a.empty) :
  list.count x (℘ a.g) =
  list.count x ℘(subgrid a.g (compute_bounds a) (compute_bounds_pres_overlaid _)) :=
begin
  rw @count_split _ _ _ a.g (compute_bounds a) (compute_bounds_pres_overlaid _),
  rw count_uneq_in_subgrid' h,
  refl
end

lemma count_nonempty_make_canonical {a : cautomaton α} {x} (h : x ≠ a.empty) :
  count a x = count (make_canonical a) x :=
begin
  unfold make_canonical count count_grid,
  simp only [cautomaton.g],
  unfold_coes, rw gen_aof_eq_gen,
  exact count_nonempty_compute_bounds h
end

end counting

namespace cardinals

section cardinals

variables {α : Type} [decidable_eq α] (a : cautomaton α) (p : point)
          (neigh : point → list point)

def neigh_with_NW := ∀p : point, point.mk (p.x - 1) (p.y - 1) ∈ neigh p

def neigh_with_N  := ∀p : point, point.mk p.x       (p.y - 1) ∈ neigh p

def neigh_with_NE := ∀p : point, point.mk (p.x + 1) (p.y - 1) ∈ neigh p

def neigh_with_W  := ∀p : point, point.mk (p.x - 1) p.y       ∈ neigh p

def neigh_with_E  := ∀p : point, point.mk (p.x + 1) p.y       ∈ neigh p

def neigh_with_SW := ∀p : point, point.mk (p.x - 1) (p.y + 1) ∈ neigh p

def neigh_with_S  := ∀p : point, point.mk p.x       (p.y + 1) ∈ neigh p

def neigh_with_SE := ∀p : point, point.mk (p.x + 1) (p.y + 1) ∈ neigh p

open cautomatons

lemma neumann_N : neigh_with_N neumann :=
  λ⟨x, y⟩, by simp [neumann]

lemma neumann_W : neigh_with_W neumann :=
  λ⟨x, y⟩, by simp [neumann]

lemma neumann_E : neigh_with_E neumann :=
  λ⟨x, y⟩, by simp [neumann]

lemma neumann_S : neigh_with_S neumann :=
  λ⟨x, y⟩, by simp [neumann]

lemma moore_NW : neigh_with_NW moore :=
  λ⟨x, y⟩, by simp [moore]

lemma moore_N : neigh_with_N moore :=
  λ⟨x, y⟩, by simp [moore]

lemma moore_NE : neigh_with_NE moore :=
  λ⟨x, y⟩, by simp [moore]

lemma moore_W : neigh_with_W moore :=
  λ⟨x, y⟩, by simp [moore]

lemma moore_E : neigh_with_E moore :=
  λ⟨x, y⟩, by simp [moore]

lemma moore_SW : neigh_with_SW moore :=
  λ⟨x, y⟩, by simp [moore]

lemma moore_S : neigh_with_S moore :=
  λ⟨x, y⟩, by simp [moore]

lemma moore_SE : neigh_with_SE moore :=
  λ⟨x, y⟩, by simp [moore]

def NW (h : neigh_with_NW a.neigh) := yield_at a ⟨p.x - 1, p.y - 1⟩

def N (h : neigh_with_N a.neigh) := yield_at a ⟨p.x, p.y - 1⟩

def NE (h : neigh_with_NE a.neigh) := yield_at a ⟨p.x + 1, p.y - 1⟩

def W (h : neigh_with_W a.neigh) := yield_at a ⟨p.x - 1, p.y⟩

def E (h : neigh_with_E a.neigh) := yield_at a ⟨p.x + 1, p.y⟩

def SW (h : neigh_with_SW a.neigh) := yield_at a ⟨p.x - 1, p.y + 1⟩

def S (h : neigh_with_S a.neigh) := yield_at a ⟨p.x, p.y + 1⟩

def SE (h : neigh_with_SE a.neigh) := yield_at a ⟨p.x + 1, p.y + 1⟩

end cardinals

end cardinals