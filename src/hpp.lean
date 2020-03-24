import cautomaton utils data.list.perm

open utils

namespace hpp

section hpp

inductive cellT | X | N | W | E | S
                | NW | NE | NS | WS | WE | ES
                | NWE | NWS | NES | WES | NWSE

inductive cardinal | CN | CW | CE | CS

open cellT cardinal

def cellT_str : cellT → string 
	| N    := "↑"
	| W    := "←"
	| E    := "→"
	| S    := "↓"
  | NW   := "↖"
  | NE   := "↗"
  | NS   := "↕"
  | WS   := "↙"
  | WE   := "↔"
  | ES   := "↙"
  | NWE  := "⊥"
  | NWS  := "⊣"
  | NES  := "⊢"
  | WES  := "⊤"
  | NWSE := "+"
  | X    := " "

def num_particles : cellT → ℕ
| N    := 1
| W    := 1
| E    := 1
| S    := 1
| NW   := 2
| NE   := 2
| NS   := 2
| WS   := 2
| WE   := 2
| ES   := 2
| NWE  := 3
| NWS  := 3
| NES  := 3
| WES  := 3
| NWSE := 4
| X    := 0

instance cellT_to_str : has_to_string cellT := ⟨cellT_str⟩

instance cellT_repr : has_repr cellT := ⟨cellT_str⟩

instance cellT_deceq : decidable_eq cellT :=
	λl r, by cases l; cases r; try {exact is_true rfl}; apply is_false; trivial

attribute [reducible]
def hpp := cautomaton cellT

def has_cardinal : cellT → cardinal → bool
  | N CN := tt
  | N _  := ff
  | W CW := tt
  | W _  := ff
  | E CE := tt
  | E _  := ff
  | S CS := tt
  | S _  := ff
  | NW CN := tt
  | NW CW := tt
  | NW _  := ff
  | NE CN := tt
  | NE CE := tt
  | NE _  := ff
  | NS CW := tt
  | NS CE := tt
  | NS _  := ff
  | WS CW := tt
  | WS CS := tt
  | WS _  := ff
  | WE CS := tt
  | WE CN := tt
  | WE _  := ff
  | ES CE := tt
  | ES CS := tt
  | ES _  := ff
  | NWE CN := tt
  | NWE CW := tt
  | NWE CE := tt
  | NWE _  := ff
  | NWS CN := tt
  | NWS CW := tt
  | NWS CS := tt
  | NWS _  := ff
  | NES CN := tt
  | NES CE := tt
  | NES CS := tt
  | NES _  := ff
  | WES CW := tt
  | WES CE := tt
  | WES CS := tt
  | WES _  := ff
  | NWSE _ := tt
  | X _ := ff

def collision : cellT → cellT
  | NS := WE
  | WE := NS
  | x  := x

def translation' : bool → bool → bool → bool → cellT
  | tt tt tt tt := NWSE
  | tt tt tt ff := WES
  | tt tt ff tt := NES
  | tt tt ff ff := ES
  | tt ff tt tt := NWS
  | tt ff tt ff := WS
  | tt ff ff tt := NS
  | tt ff ff ff := S
  | ff tt tt tt := NWE
  | ff tt tt ff := WE
  | ff tt ff tt := NE
  | ff tt ff ff := E
  | ff ff tt tt := NW
  | ff ff tt ff := W
  | ff ff ff tt := N
  | ff ff ff ff := X

def translation (neigh : list cellT) : cellT :=
  let north := list.nth neigh 0 in
  let west  := list.nth neigh 1 in
  let east  := list.nth neigh 2 in
  let south := list.nth neigh 3 in
  match north with
    | none     := X
    | (some n) :=
  match west with
    | none     := X
    | (some w) :=
  match east with
    | none     := X
    | (some e) :=   
  match south with
    | none     := X
    | (some s) :=
      translation' (has_cardinal n CS)
                   (has_cardinal w CE)
                   (has_cardinal e CW)
                   (has_cardinal s CN)
  end end end end

lemma translation_eq_translation' {neigh : list cellT}
  (h : list.length neigh = 4) :
  translation neigh =
    let n := list.nth_le neigh 0 $ by simp [h]; exact dec_trivial in
    let w := list.nth_le neigh 1 $ by simp [h]; exact dec_trivial in
    let e := list.nth_le neigh 2 $ by simp [h]; exact dec_trivial in
    let s := list.nth_le neigh 3 $ by simp [h]; exact dec_trivial in
      translation' (has_cardinal n CS)
                   (has_cardinal w CE)
                   (has_cardinal e CW)
                   (has_cardinal s CN) :=
begin
  cases neigh with x₁ xs₁, cases h,
  cases xs₁ with x₂ xs₂, cases h,
  cases xs₂ with x₃ xs₃, cases h,
  cases xs₃ with x₄ xs₄, cases h,
  cases xs₄ with x₅ xs₅, swap 2, cases h,
  unfold translation, simp,
  delta translation, simp
end

def mk_hpp (g : vec_grid₀ cellT) : hpp :=
  ⟨g, X, cautomatons.neumann, sum.inl cautomatons.ext_one, (λ_ neigh, translation neigh)⟩

def hpp_g :=
  vec_grid₀.mk
    ⟨11, 11, dec_trivial,
    ⟨[X, X, X, X, X, X, X, X, X, X, X,
      X, X, X, X, X, X, X, X, X, X, X,
      X, X, X, X, X, X, X, X, X, X, X,
      X, X, X, X, X, WE, X, X, X, S, X,
      E, X, X, X, E, X, W, X, X, N, N,
      X, X, X, X, X, N, X, X, X, X, X,
      X, X, X, X, X, X, X, X, X, X, X,
      X, X, X, X, X, X, X, X, X, X, X,
      X, X, X, X, X, X, X, X, X, X, X,
      X, X, X, X, X, X, X, X, X, X, X,
      X, X, X, X, X, X, X, X, X, X, X], rfl⟩⟩
    ⟨0, 0⟩ 

def simple := mk_hpp hpp_g

#eval step_n simple 8

def hpp_g' :=
  vec_grid₀.mk
    ⟨11, 11, dec_trivial,
    ⟨[X, X, X, X, X, X, X, X, X, X, X,
      X, X, X, X, X, X, X, X, X, X, X,
      X, X, X, X, X, X, X, X, X, X, X,
      X, X, X, X, X, X, X, X, X, X, X,
      X, X, X, X, X, X, X, X, X, X, X,
      X, X, X, X, X, X, X, X, X, X, X,
      X, X, X, X, X, X, X, X, X, X, X,
      X, X, X, X, X, X, X, X, X, X, X,
      X, X, X, X, X, X, X, X, X, X, X,
      X, X, X, X, X, X, X, X, X, X, X,
      X, X, X, X, X, X, X, X, X, X, X], rfl⟩⟩
    ⟨0, 0⟩ 

def test_simple := mk_hpp hpp_g'

def count_particles (a : hpp) : ℕ :=
  list.sum ℘(num_particles <$> a.g)

def count_particles' (a : hpp) : ℕ :=
  count a N + count a W + count a S + count a E +
  2 * count a NW + 2 * count a NE + 2 * count a NS + 2 * count a WS +
  2 * count a WE + 2 * count a ES + 3 * count a NWE + 3 * count a NWS +
  3 * count a NES + 3 * count a WES + 4 * count a NWSE

def option_coerce : option cellT → cellT
  | option.none := X
  | (option.some c) := c

instance : has_coe (option cellT) cellT := ⟨option_coerce⟩

set_option pp.binder_types false

open list

lemma count_particles_split_dir {g} (a : hpp) (h : a = mk_hpp g) :
  count_particles' a = count_particles a :=
begin
  subst h, simp [mk_hpp],
  simp [count_particles, count_particles', _root_.count, count_grid],
  rw ← map_generate_map_v₀, 
  repeat { rw generate_eq_data },
  rcases g with ⟨⟨r, c, h, ⟨data, hdata⟩⟩, o⟩,
  simp, clear hdata,
  induction data with hd tl ih,
    {simp [list.count]},
    {
      by_cases eq₁ : hd = E; simp [eq₁],
        {
          rw @count_cons_self _ _ E,
          repeat { rw @count_cons_of_ne _ _ _ E _ tl }; try { trivial },
          unfold num_particles, rw ← ih, rw nat.succ_add,
          rw nat.one_add
        },
        {
      by_cases eq₂ : hd = N,
        {
          subst eq₂,
          rw @count_cons_self _ _ N,
          repeat { rw @count_cons_of_ne _ _ _ N _ tl }; try { trivial },
          unfold num_particles, rw ← ih, rw nat.succ_add,
          rw nat.one_add
        },
        {
      by_cases eq₃ : hd = S,
        {
          subst eq₃,
          rw @count_cons_self _ _ S,
          repeat { rw @count_cons_of_ne _ _ _ S _ tl }; try { trivial },
          unfold num_particles, rw ← ih, rw nat.succ_add,
          rw nat.one_add, ring
        },
        {
      by_cases eq₄ : hd = W,
        {
          subst eq₄,
          rw @count_cons_self _ _ W,
          repeat { rw @count_cons_of_ne _ _ _ W _ tl }; try { trivial },
          unfold num_particles, rw ← ih, rw nat.succ_add,
          rw nat.one_add, ring
        },
        {
      by_cases eq₅ : hd = ES,
        {
          subst eq₅, unfold num_particles,
          rw @count_cons_self _ _ ES, repeat { rw ← nat.one_add },
          repeat { rw @count_cons_of_ne _ _ _ ES _ tl }; try { trivial },
          rw ← ih, ring
        },
        {
      by_cases eq₆ : hd = NE,
        {
          subst eq₆, unfold num_particles,
          rw @count_cons_self _ _ NE, repeat { rw ← nat.one_add },
          repeat { rw @count_cons_of_ne _ _ _ NE _ tl }; try { trivial },
          rw ← ih, ring
        },
        {
      by_cases eq₇ : hd = NS,
        {
          subst eq₇, unfold num_particles,
          rw @count_cons_self _ _ NS, repeat { rw ← nat.one_add },
          repeat { rw @count_cons_of_ne _ _ _ NS _ tl }; try { trivial },
          rw ← ih, ring
        },
        {
      by_cases eq₈ : hd = NW,
        {
          subst eq₈, unfold num_particles,
          rw @count_cons_self _ _ NW, repeat { rw ← nat.one_add },
          repeat { rw @count_cons_of_ne _ _ _ NW _ tl }; try { trivial },
          rw ← ih, ring
        },
        {
      by_cases eq₉ : hd = WE,
        {
          subst eq₉, unfold num_particles,
          rw @count_cons_self _ _ WE, repeat { rw ← nat.one_add },
          repeat { rw @count_cons_of_ne _ _ _ WE _ tl }; try { trivial },
          rw ← ih, ring
        },
        {
      by_cases eq₁₀ : hd = NES,
        {
          subst eq₁₀, unfold num_particles,
          rw @count_cons_self _ _ NES, repeat { rw ← nat.one_add },
          repeat { rw @count_cons_of_ne _ _ _ NES _ tl }; try { trivial },
          rw ← ih, ring
        },
        {
      by_cases eq₁₁ : hd = NWE,
        {
          subst eq₁₁, unfold num_particles,
          rw @count_cons_self _ _ NWE, repeat { rw ← nat.one_add },
          repeat { rw @count_cons_of_ne _ _ _ NWE _ tl }; try { trivial },
          rw ← ih, ring
        },
        {
      by_cases eq₁₂ : hd = NWS,
        {
          subst eq₁₂, unfold num_particles,
          rw @count_cons_self _ _ NWS, repeat { rw ← nat.one_add },
          repeat { rw @count_cons_of_ne _ _ _ NWS _ tl }; try { trivial },
          rw ← ih, ring
        },
        {
      by_cases eq₁₃ : hd = WES,
        {
          subst eq₁₃, unfold num_particles,
          rw @count_cons_self _ _ WES, repeat { rw ← nat.one_add },
          repeat { rw @count_cons_of_ne _ _ _ WES _ tl }; try { trivial },
          rw ← ih, ring
        },
        {
      by_cases eq₁₄ : hd = NWSE,
        {
          subst eq₁₄, unfold num_particles,
          rw @count_cons_self _ _ NWSE, repeat { rw ← nat.one_add },
          repeat { rw @count_cons_of_ne _ _ _ NWSE _ tl }; try { trivial },
          rw ← ih, ring
        },
        {
      by_cases eq₁₅ : hd = WS,
        {
          subst eq₁₅, unfold num_particles,
          rw @count_cons_self _ _ WS, repeat { rw ← nat.one_add },
          repeat { rw @count_cons_of_ne _ _ _ WS _ tl }; try { trivial },
          rw ← ih, ring
        },
        {
          have : hd = X, { cases hd; try { trivial } }, subst this,
          repeat { rw @count_cons_of_ne _ _ _ X _ tl }; try { trivial },
          unfold num_particles,
          rw zero_add, rw ← ih,
        }}}}}}}}}}}}}}}
    }
end

theorem canonical_pres_count {g} (a : hpp) (h : a = mk_hpp g) :
  count_particles a = count_particles (make_canonical a) :=
begin
  rw ← count_particles_split_dir _ h,
  rw ← count_particles_split_dir,
  have h₁ : a.empty = X, by finish,
  unfold count_particles',
  repeat { rw ← count_nonempty_make_canonical },
  all_goals { try { rw h₁; trivial } },
  swap 2, exact (make_canonical a).g, simp [mk_hpp],
  simp [make_canonical], subst h, simp [mk_hpp]
end

lemma next_gen_ext_one_gbl_y {a : hpp}
  (h : a.bound = sum.inl cautomatons.ext_one) :
  (grid.bl (ext_aut a).g).y = (grid.bl a.g).y - 1 :=
begin
  simp [ext_aut, h, grid.bl],
  unfold_coes,
  simp [vec_grid₀_of_fgrid₀_o, cautomatons.bl_ext_one, grid_bounds, grid.bl]
end

lemma next_gen_ext_one_gbl_x {a : hpp}
  (h : a.bound = sum.inl cautomatons.ext_one) :
  (grid.bl (ext_aut a).g).x = (grid.bl a.g).x - 1 :=
begin
  simp [ext_aut, h, grid.bl],
  unfold_coes,
  simp [vec_grid₀_of_fgrid₀_o, cautomatons.bl_ext_one, grid_bounds, grid.bl]
end

lemma next_gen_ext_one_gtr_y {a : hpp}
  (h : a.bound = sum.inl cautomatons.ext_one) :
  (gtr ((ext_aut a).g)).y = (gtr a.g).y + 1 :=
begin
  simp [ext_aut, h, expand_gtr, grid.bl],
  unfold_coes,
  simp [vec_grid₀_of_fgrid₀_o, vec_grid₀_of_fgrid₀, relative_grid.rows],
  simp [cautomatons.bl_ext_one, cautomatons.rows_of_box_ext_one,
  rows_of_box, cautomatons.tr_ext_one, grid_bounds, grid.bl, expand_gtr,
  relative_grid.rows],
  rw int.nat_abs_of_nonneg,
  ring, simp
end

end hpp

end hpp